package blockstm

import (
	"bytes"

	storetypes "cosmossdk.io/store/types"

	"github.com/cosmos/cosmos-sdk/blockstm/tree"
)

const (
	OuterBTreeDegree = 4 // Since we do copy-on-write a lot, smaller degree means smaller allocations
	InnerBTreeDegree = 4

	// maxValueSnapshotBytes caps value snapshotting (pre-state cache / captured bytes) for validation.
	// Larger values skip snapshotting and rely on version-based validation.
	maxValueSnapshotBytes = 16 << 10 // 16KiB
)

type MVData = GMVData[[]byte]

func NewMVData() *MVData {
	return NewGMVData(storetypes.BytesIsZero, storetypes.BytesValueLen, bytes.Equal)
}

type GMVData[V any] struct {
	index    *mvIndex[V]
	isZero   func(V) bool
	valueLen func(V) int
	eq       func(V, V) bool
}

func (d *GMVData[V]) shouldSnapshotValue(value V) bool {
	if d.valueLen == nil {
		return false
	}
	sz := d.valueLen(value)
	return sz >= 0 && sz <= maxValueSnapshotBytes
}

func NewMVStore(key storetypes.StoreKey) MVStore {
	switch key.(type) {
	case *storetypes.ObjectStoreKey:
		// Object stores don't necessarily have a deterministic equality relation.
		// Keep version-based validation by default.
		return NewGMVData(storetypes.AnyIsZero, storetypes.AnyValueLen, nil)
	default:
		return NewGMVData(storetypes.BytesIsZero, storetypes.BytesValueLen, bytes.Equal)
	}
}

func NewGMVData[V any](isZero func(V) bool, valueLen func(V) int, eq func(V, V) bool) *GMVData[V] {
	d := &GMVData[V]{
		index:    newMVIndex[V](),
		isZero:   isZero,
		valueLen: valueLen,
		eq:       eq,
	}
	return d
}

// getTree returns `nil` if not found.
func (d *GMVData[V]) getTree(key Key) *tree.BTree[secondaryDataItem[V]] {
	return d.index.get(key)
}

// getTreeOrDefault sets a new tree atomically if not found.
func (d *GMVData[V]) getTreeOrDefault(key Key) *tree.BTree[secondaryDataItem[V]] {
	return d.index.getOrCreate(key)
}

func (d *GMVData[V]) Write(key Key, value V, version TxnVersion) {
	tree := d.getTreeOrDefault(key)
	tree.Set(secondaryDataItem[V]{Index: ToShiftedIndex(version.Index), Incarnation: version.Incarnation, Value: value})
}

func (d *GMVData[V]) WriteEstimate(key Key, txn TxnIndex) {
	tree := d.getTreeOrDefault(key)
	tree.Set(secondaryDataItem[V]{Index: ToShiftedIndex(txn), Estimate: true})
}

func (d *GMVData[V]) Delete(key Key, txn TxnIndex) {
	tree := d.getTreeOrDefault(key)
	tree.Delete(secondaryDataItem[V]{Index: ToShiftedIndex(txn)})
}

func (d *GMVData[V]) CacheStorageValue(key Key, value V) {
	// Storage pre-state caching is only used to support value-based validation.
	// For large values, skip caching and fall back to version-based validation.
	if d.eq == nil || !d.shouldSnapshotValue(value) {
		return
	}
	tree := d.getTreeOrDefault(key)
	tree.Set(secondaryDataItem[V]{Index: 0, Value: value})
}

// Read returns the value and the version of the value that's less than the given txn.
// If the key is not found, returns `(zero, InvalidTxnVersion, false)`.
// If the key is found but value is an estimate, returns `(value, version, true)`.
// If the key is found, returns `(value, version, false)`, `value` can be zero value which means deleted.
func (d *GMVData[V]) Read(key Key, txn TxnIndex) (V, TxnVersion, bool) {
	var zero V
	if txn <= 0 {
		return zero, InvalidTxnVersion, false
	}

	inner := d.getTree(key)
	if inner == nil {
		return zero, InvalidTxnVersion, false
	}

	// find the closest txn that's less than the given txn
	item, ok := seekClosestTxn(inner, txn)
	if !ok {
		return zero, InvalidTxnVersion, false
	}

	// Index 0 corresponds to the pre-state from storage (InvalidTxnVersion).
	if item.Index == 0 {
		return item.Value, InvalidTxnVersion, item.Estimate
	}

	return item.Value, item.Version(), item.Estimate
}

func (d *GMVData[V]) Iterator(
	opts IteratorOptions, txn TxnIndex,
	waitFn func(TxnIndex),
) *MVIterator[V] {
	keys := d.index.snapshotKeys(opts.Start, opts.End, opts.Ascending)
	return NewMVIterator(opts, txn, d, keys, waitFn)
}

// ValidateReadSet validates the read descriptors,
// returns true if valid.
func (d *GMVData[V]) ValidateReadSet(txn TxnIndex, tmp any, delayed bool) bool {
	rs := tmp.(*ReadSet[V])

	if delayed {
		for _, desc := range rs.DelayedReads {
			if !d.validateRead(desc, txn) {
				return false
			}
		}
		return true
	}

	for _, desc := range rs.Reads {
		if !d.validateRead(desc, txn) {
			return false
		}
	}

	for _, desc := range rs.Iterators {
		if !d.validateIterator(desc, txn) {
			return false
		}
	}

	return true
}

func (d *GMVData[V]) validateRead(desc ReadDescriptor[V], txn TxnIndex) bool {
	v, version, estimate := d.Read(desc.Key, txn)
	if estimate {
		// previously read entry from data, now ESTIMATE
		return false
	}

	if desc.Validate(v, version) {
		return true
	}

	// If the original read was from storage (InvalidTxnVersion) and now resolves to a
	// versioned value, allow validation to pass if the value matches the cached
	// pre-state (storage) value stored at internal index 0.
	//
	// This avoids re-reading from storage during validation for value-based checks.
	if desc.Predicate == nil && !desc.Version.Valid() && version.Valid() && d.eq != nil {
		if inner := d.getTree(desc.Key); inner != nil {
			if item, ok := inner.Get(secondaryDataItem[V]{Index: 0}); ok {
				if d.eq(v, item.Value) {
					return true
				}
			}
		}
	}

	return false
}

// validateIterator validates the iteration descriptor by replaying and compare the recorded reads.
// returns true if valid.
func (d *GMVData[V]) validateIterator(desc IteratorDescriptor[V], txn TxnIndex) bool {
	keys := d.index.snapshotKeys(desc.Start, desc.End, desc.Ascending)
	it := NewMVIterator(desc.IteratorOptions, txn, d, keys, nil)
	defer it.Close()

	var i int
	for ; it.Valid(); it.Next() {
		if desc.Stop != nil {
			if BytesBeyond(it.Key(), desc.Stop, desc.Ascending) {
				break
			}
		}

		if i >= len(desc.Reads) {
			return false
		}

		read := desc.Reads[i]
		if !bytes.Equal(read.Key, it.Key()) {
			return false
		}
		if !read.Validate(it.Value(), it.Version()) {
			return false
		}

		i++
	}

	// we read an estimate value, fail the validation.
	if it.ReadEstimateValue() {
		return false
	}

	return i == len(desc.Reads)
}

func (d *GMVData[V]) Snapshot() (snapshot []GKVPair[V]) {
	d.SnapshotTo(func(key Key, value V) bool {
		snapshot = append(snapshot, GKVPair[V]{key, value})
		return true
	})
	return snapshot
}

func (d *GMVData[V]) SnapshotTo(cb func(Key, V) bool) {
	keys := d.index.snapshotAllKeys(true)
	for i := 0; i < len(keys); i++ {
		inner := d.getTree(keys[i])
		if inner == nil {
			continue
		}
		item, ok := inner.Max()
		if !ok {
			continue
		}
		if item.Estimate {
			continue
		}
		if !cb(keys[i], item.Value) {
			return
		}
	}
}

func (d *GMVData[V]) SnapshotToStore(store storetypes.Store) {
	kv := store.(storetypes.GKVStore[V])
	d.SnapshotTo(func(key Key, value V) bool {
		if d.isZero(value) {
			kv.Delete(key)
		} else {
			kv.Set(key, value)
		}
		return true
	})
}

type GKVPair[V any] struct {
	Key   Key
	Value V
}
type KVPair = GKVPair[[]byte]

type dataItem[V any] struct {
	Key  Key
	Tree *tree.BTree[secondaryDataItem[V]]
}

func (d *dataItem[V]) Init() {
	if d.Tree == nil {
		d.Tree = tree.NewBTree(secondaryLesser[V], InnerBTreeDegree)
	}
}

var _ tree.KeyItem = dataItem[[]byte]{}

func (item dataItem[V]) GetKey() []byte {
	return item.Key
}

type secondaryDataItem[V any] struct {
	Index       ShiftedTxnIndex
	Incarnation Incarnation
	Value       V
	Estimate    bool
}

func secondaryLesser[V any](a, b secondaryDataItem[V]) bool {
	return a.Index < b.Index
}

func (item secondaryDataItem[V]) Version() TxnVersion {
	return TxnVersion{Index: FromShiftedIndex(item.Index), Incarnation: item.Incarnation}
}

// seekClosestTxn returns the closest txn that's less than the given txn.
func seekClosestTxn[V any](tree *tree.BTree[secondaryDataItem[V]], txn TxnIndex) (secondaryDataItem[V], bool) {
	return tree.ReverseSeek(secondaryDataItem[V]{Index: ToShiftedIndex(txn - 1)})
}
