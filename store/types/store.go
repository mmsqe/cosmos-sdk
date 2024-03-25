package types

import (
	"fmt"
	"io"
	"slices"

	crypto "github.com/cometbft/cometbft/api/cometbft/crypto/v1"

	corestore "cosmossdk.io/core/store"
	"cosmossdk.io/store/metrics"
	pruningtypes "cosmossdk.io/store/pruning/types"
	snapshottypes "cosmossdk.io/store/snapshots/types"
)

type Store interface {
	GetStoreType() StoreType
	CacheWrapper
}

// Committer is something that can persist to disk
type Committer interface {
	Commit() CommitID
	LastCommitID() CommitID
	LatestVersion() int64

	// WorkingHash returns the hash of the KVStore's state before commit.
	WorkingHash() []byte

	SetPruning(pruningtypes.PruningOptions)
	GetPruning() pruningtypes.PruningOptions
}

type PausablePruner interface {
	// PausePruning let the pruning handler know that the store is being committed
	// or not, so the handler can decide to prune or not the store.
	//
	// NOTE: PausePruning(true) should be called before Commit() and PausePruning(false)
	PausePruning(bool)
}

// CommitStore represents a store that can be committed and provides basic store operations.
// It combines the functionality of Committer and Store interfaces.
// Stores of MultiStore must implement CommitStore.
type CommitStore interface {
	Committer
	Store
}

// Queryable allows a Store to expose internal state to the abci.Query
// interface. Multistore can route requests to the proper Store.
//
// This is an optional, but useful extension to any CommitStore
type Queryable interface {
	Query(*RequestQuery) (*ResponseQuery, error)
}

type RequestQuery struct {
	Data   []byte
	Path   string
	Height int64
	Prove  bool
}

type ResponseQuery struct {
	Code      uint32
	Log       string
	Info      string
	Index     int64
	Key       []byte
	Value     []byte
	ProofOps  *crypto.ProofOps
	Height    int64
	Codespace string
}

//----------------------------------------
// MultiStore

// StoreUpgrades defines a series of transformations to apply the multistore db upon load
type StoreUpgrades struct {
	Added   []string      `json:"added"`
	Renamed []StoreRename `json:"renamed"`
	Deleted []string      `json:"deleted"`
}

// StoreRename defines a name change of a sub-store.
// All data previously under a PrefixStore with OldKey will be copied
// to a PrefixStore with NewKey, then deleted from OldKey store.
type StoreRename struct {
	OldKey string `json:"old_key"`
	NewKey string `json:"new_key"`
}

// IsAdded returns true if the given key should be added
func (s *StoreUpgrades) IsAdded(key string) bool {
	if s == nil {
		return false
	}
	return slices.Contains(s.Added, key)
}

// IsDeleted returns true if the given key should be deleted
func (s *StoreUpgrades) IsDeleted(key string) bool {
	if s == nil {
		return false
	}
	return slices.Contains(s.Deleted, key)
}

// RenamedFrom returns the oldKey if it was renamed
// Returns "" if it was not renamed
func (s *StoreUpgrades) RenamedFrom(key string) string {
	if s == nil {
		return ""
	}
	for _, re := range s.Renamed {
		if re.NewKey == key {
			return re.OldKey
		}
	}
	return ""
}

type MultiStore interface {
	Store

	// CacheMultiStore branches MultiStore into a cached storage object.
	// NOTE: Caller should probably not call .Write() on each, but
	// call CacheMultiStore.Write().
	CacheMultiStore() CacheMultiStore

	// CacheMultiStoreWithVersion branches the underlying MultiStore where
	// each stored is loaded at a specific version (height).
	CacheMultiStoreWithVersion(version int64) (CacheMultiStore, error)

	// GetStore is convenience for fetching substores.
	// If the store does not exist, panics.
	GetStore(StoreKey) Store
	GetKVStore(StoreKey) KVStore
	GetObjKVStore(StoreKey) ObjKVStore

	// TracingEnabled returns if tracing is enabled for the MultiStore.
	TracingEnabled() bool

	// SetTracer sets the tracer for the MultiStore that the underlying
	// stores will utilize to trace operations. The modified MultiStore is
	// returned.
	SetTracer(w io.Writer) MultiStore

	// SetTracingContext sets the tracing context for a MultiStore. It is
	// implied that the caller should update the context when necessary between
	// tracing operations. The modified MultiStore is returned.
	SetTracingContext(TraceContext) MultiStore

	// LatestVersion returns the latest version in the store
	LatestVersion() int64
}

// CacheMultiStore is from MultiStore.CacheMultiStore()....
type CacheMultiStore interface {
	MultiStore
	Write() // Writes operations to underlying KVStore
}

// CommitMultiStore is an interface for a MultiStore without cache capabilities.
type CommitMultiStore interface {
	Committer
	MultiStore
	snapshottypes.Snapshotter

	// MountStoreWithDB mount a store of type using the given db.
	// If db == nil, the new store will use the CommitMultiStore db.
	MountStoreWithDB(key StoreKey, typ StoreType, db corestore.KVStoreWithBatch)

	// GetCommitStore panics on a nil key.
	GetCommitStore(key StoreKey) CommitStore

	// GetCommitKVStore panics on a nil key.
	GetCommitKVStore(key StoreKey) CommitKVStore

	// LoadLatestVersion load the latest persisted version. Called once after all calls to
	// Mount*Store() are complete.
	LoadLatestVersion() error

	// LoadLatestVersionAndUpgrade will load the latest version, but also
	// rename/delete/create sub-store keys, before registering all the keys
	// in order to handle breaking formats in migrations
	LoadLatestVersionAndUpgrade(upgrades *StoreUpgrades) error

	// LoadVersionAndUpgrade will load the named version, but also
	// rename/delete/create sub-store keys, before registering all the keys
	// in order to handle breaking formats in migrations
	LoadVersionAndUpgrade(ver int64, upgrades *StoreUpgrades) error

	// LoadVersion load a specific persisted version. When you load an old version, or when
	// the last commit attempt didn't complete, the next commit after loading
	// must be idempotent (return the same commit id). Otherwise the behavior is
	// undefined.
	LoadVersion(ver int64) error

	// SetInterBlockCache set an inter-block (persistent) cache that maintains a mapping from
	// StoreKeys to CommitKVStores.
	SetInterBlockCache(MultiStorePersistentCache)

	// SetInitialVersion sets the initial version of the IAVL tree. It is used when
	// starting a new chain at an arbitrary height.
	SetInitialVersion(version int64) error

	// SetIAVLCacheSize sets the cache size of the IAVL tree.
	SetIAVLCacheSize(size int)

	// SetIAVLDisableFastNode enables/disables fastnode feature on iavl.
	SetIAVLDisableFastNode(disable bool)

	// SetIAVLSyncPruning set sync/async pruning on iavl.
	SetIAVLSyncPruning(sync bool)

	// RollbackToVersion rollback the db to specific version(height).
	RollbackToVersion(version int64) error

	// ListeningEnabled returns if listening is enabled for the KVStore belonging the provided StoreKey
	ListeningEnabled(key StoreKey) bool

	// AddListeners adds a listener for the KVStore belonging to the provided StoreKey
	AddListeners(keys []StoreKey)

	// PopStateCache returns the accumulated state change messages from the CommitMultiStore
	PopStateCache() []*StoreKVPair

	// SetMetrics sets the metrics for the KVStore
	SetMetrics(metrics metrics.StoreMetrics)
}

//---------subsp-------------------------------
// KVStore

// GBasicKVStore is a simple interface to get/set data
type GBasicKVStore[V any] interface {
	// Get returns nil if key doesn't exist. Panics on nil key.
	Get(key []byte) V

	// Has checks if a key exists. Panics on nil key.
	Has(key []byte) bool

	// Set sets the key. Panics on nil key or value.
	Set(key []byte, value V)

	// Delete deletes the key. Panics on nil key.
	Delete(key []byte)
}

// GKVStore additionally provides iteration and deletion
type GKVStore[V any] interface {
	Store
	GBasicKVStore[V]

	// Iterator over a domain of keys in ascending order. End is exclusive.
	// Start must be less than end, or the Iterator is invalid.
	// Iterator must be closed by caller.
	// To iterate over entire domain, use store.Iterator(nil, nil)
	// CONTRACT: No writes may happen within a domain while an iterator exists over it.
	// Exceptionally allowed for cachekv.Store, safe to write in the modules.
	Iterator(start, end []byte) GIterator[V]

	// ReverseIterator iterates over a domain of keys in descending order. End is exclusive.
	// Start must be less than end, or the Iterator is invalid.
	// Iterator must be closed by caller.
	// CONTRACT: No writes may happen within a domain while an iterator exists over it.
	// Exceptionally allowed for cachekv.Store, safe to write in the modules.
	ReverseIterator(start, end []byte) GIterator[V]
}

// GIterator is the generic version of dbm's Iterator
type GIterator[V any] interface {
	// Domain returns the start (inclusive) and end (exclusive) limits of the iterator.
	// CONTRACT: start, end readonly []byte
	Domain() (start, end []byte)

	// Valid returns whether the current iterator is valid. Once invalid, the Iterator remains
	// invalid forever.
	Valid() bool

	// Next moves the iterator to the next key in the database, as defined by order of iteration.
	// If Valid returns false, this method will panic.
	Next()

	// Key returns the key at the current position. Panics if the iterator is invalid.
	// CONTRACT: key readonly []byte
	Key() (key []byte)

	// Value returns the value at the current position. Panics if the iterator is invalid.
	// CONTRACT: value readonly []byte
	Value() (value V)

	// Error returns the last error encountered by the iterator, if any.
	Error() error

	// Close closes the iterator, relasing any allocated resources.
	Close() error
}

type (
	Iterator     = GIterator[[]byte]
	BasicKVStore = GBasicKVStore[[]byte]
	KVStore      = GKVStore[[]byte]

	ObjIterator     = GIterator[any]
	ObjBasicKVStore = GBasicKVStore[any]
	ObjKVStore      = GKVStore[any]
)

// CacheKVStore branches a KVStore and provides read cache functionality.
// After calling .Write() on the CacheKVStore, all previously created
// CacheKVStores on the object expire.
type CacheKVStore interface {
	KVStore

	// Write writes operations to underlying KVStore
	Write()
}

// CommitKVStore is an interface for MultiStore.
type CommitKVStore interface {
	Committer
	KVStore
}

//----------------------------------------
// CacheWrap

// CacheWrap is the most appropriate interface for store ephemeral branching and cache.
// For example, IAVLStore.CacheWrap() returns a CacheKVStore. CacheWrap should not return
// a Committer, since Commit ephemeral store make no sense. It can return KVStore,
// HeapStore, SpaceStore, etc.
type CacheWrap interface {
	CacheWrapper

	// Write syncs with the underlying store.
	Write()
}

type CacheWrapper interface {
	// CacheWrap branches a store.
	CacheWrap() CacheWrap

	// CacheWrapWithTrace branches a store with tracing enabled.
	CacheWrapWithTrace(w io.Writer, tc TraceContext) CacheWrap
}

func (cid CommitID) IsZero() bool {
	return cid.Version == 0 && len(cid.Hash) == 0
}

func (cid CommitID) String() string {
	return fmt.Sprintf("CommitID{%v:%X}", cid.Hash, cid.Version)
}

//----------------------------------------
// Store types

// StoreType is kind of store
type StoreType int

const (
	StoreTypeMulti StoreType = iota
	StoreTypeDB
	StoreTypeIAVL
	StoreTypeTransient
	StoreTypeMemory
	StoreTypeSMT
	StoreTypePersistent
	StoreTypeObject
)

func (st StoreType) String() string {
	switch st {
	case StoreTypeMulti:
		return "StoreTypeMulti"

	case StoreTypeDB:
		return "StoreTypeDB"

	case StoreTypeIAVL:
		return "StoreTypeIAVL"

	case StoreTypeTransient:
		return "StoreTypeTransient"

	case StoreTypeMemory:
		return "StoreTypeMemory"

	case StoreTypeSMT:
		return "StoreTypeSMT"

	case StoreTypePersistent:
		return "StoreTypePersistent"

	case StoreTypeObject:
		return "StoreTypeObject"
	}

	return "unknown store type"
}

//----------------------------------------
// Keys for accessing substores

// StoreKey is a key used to index stores in a MultiStore.
type StoreKey interface {
	Name() string
	String() string
}

// CapabilityKey represent the Cosmos SDK keys for object-capability
// generation in the IBC protocol as defined in https://github.com/cosmos/ibc/tree/master/spec/core/ics-005-port-allocation#data-structures
type CapabilityKey StoreKey

// KVStoreKey is used for accessing substores.
// Only the pointer value should ever be used - it functions as a capabilities key.
type KVStoreKey struct {
	name string
}

// NewKVStoreKey returns a new pointer to a KVStoreKey.
// Use a pointer so keys don't collide.
func NewKVStoreKey(name string) *KVStoreKey {
	if name == "" {
		panic("empty key name not allowed")
	}
	return &KVStoreKey{
		name: name,
	}
}

// NewKVStoreKeys returns a map of new  pointers to KVStoreKey's.
// The function will panic if there is a potential conflict in names (see `assertNoPrefix`
// function for more details).
func NewKVStoreKeys(names ...string) map[string]*KVStoreKey {
	assertNoCommonPrefix(names)
	keys := make(map[string]*KVStoreKey, len(names))
	for _, n := range names {
		keys[n] = NewKVStoreKey(n)
	}

	return keys
}

func (key *KVStoreKey) Name() string {
	return key.name
}

func (key *KVStoreKey) String() string {
	return fmt.Sprintf("KVStoreKey{%p, %s}", key, key.name)
}

// TransientStoreKey is used for indexing transient stores in a MultiStore
type TransientStoreKey struct {
	name string
}

// NewTransientStoreKey constructs new TransientStoreKey
// Must return a pointer according to the ocap principle
func NewTransientStoreKey(name string) *TransientStoreKey {
	return &TransientStoreKey{
		name: name,
	}
}

// Name implements StoreKey
func (key *TransientStoreKey) Name() string {
	return key.name
}

// String implements StoreKey
func (key *TransientStoreKey) String() string {
	return fmt.Sprintf("TransientStoreKey{%p, %s}", key, key.name)
}

// ObjectStoreKey is used for indexing transient stores in a MultiStore
type ObjectStoreKey struct {
	name string
}

// Constructs new ObjectStoreKey
// Must return a pointer according to the ocap principle
func NewObjectStoreKey(name string) *ObjectStoreKey {
	return &ObjectStoreKey{
		name: name,
	}
}

// Implements StoreKey
func (key *ObjectStoreKey) Name() string {
	return key.name
}

// Implements StoreKey
func (key *ObjectStoreKey) String() string {
	return fmt.Sprintf("ObjectStoreKey{%p, %s}", key, key.name)
}

// MemoryStoreKey defines a typed key to be used with an in-memory KVStore.
type MemoryStoreKey struct {
	name string
}

func NewMemoryStoreKey(name string) *MemoryStoreKey {
	return &MemoryStoreKey{name: name}
}

// Name returns the name of the MemoryStoreKey.
func (key *MemoryStoreKey) Name() string {
	return key.name
}

// String returns a stringified representation of the MemoryStoreKey.
func (key *MemoryStoreKey) String() string {
	return fmt.Sprintf("MemoryStoreKey{%p, %s}", key, key.name)
}

//----------------------------------------

// TraceContext contains TraceKVStore context data. It will be written with
// every trace operation.
type TraceContext map[string]interface{}

// Clone clones tc into another instance of TraceContext.
func (tc TraceContext) Clone() TraceContext {
	ret := TraceContext{}
	for k, v := range tc {
		ret[k] = v
	}

	return ret
}

// Merge merges value of newTc into tc.
func (tc TraceContext) Merge(newTc TraceContext) TraceContext {
	if tc == nil {
		tc = TraceContext{}
	}

	for k, v := range newTc {
		tc[k] = v
	}

	return tc
}

// MultiStorePersistentCache defines an interface which provides inter-block
// (persistent) caching capabilities for multiple CommitKVStores based on StoreKeys.
type MultiStorePersistentCache interface {
	// GetStoreCache wrap and return the provided CommitKVStore with an inter-block (persistent)
	// cache.
	GetStoreCache(key StoreKey, store CommitKVStore) CommitKVStore

	// Unwrap return the underlying CommitKVStore for a StoreKey.
	Unwrap(key StoreKey) CommitKVStore

	// Reset the entire set of internal caches.
	Reset()
}

// StoreWithInitialVersion is a store that can have an arbitrary initial
// version.
type StoreWithInitialVersion interface {
	// SetInitialVersion sets the initial version of the IAVL tree. It is used when
	// starting a new chain at an arbitrary height.
	SetInitialVersion(version int64)
}

// NewTransientStoreKeys constructs a new map of TransientStoreKey's
// Must return pointers according to the ocap principle
// The function will panic if there is a potential conflict in names
// see `assertNoCommonPrefix` function for more details.
func NewTransientStoreKeys(names ...string) map[string]*TransientStoreKey {
	assertNoCommonPrefix(names)
	keys := make(map[string]*TransientStoreKey)
	for _, n := range names {
		keys[n] = NewTransientStoreKey(n)
	}

	return keys
}

// NewMemoryStoreKeys constructs a new map matching store key names to their
// respective MemoryStoreKey references.
// The function will panic if there is a potential conflict in names (see `assertNoPrefix`
// function for more details).
func NewMemoryStoreKeys(names ...string) map[string]*MemoryStoreKey {
	assertNoCommonPrefix(names)
	keys := make(map[string]*MemoryStoreKey)
	for _, n := range names {
		keys[n] = NewMemoryStoreKey(n)
	}

	return keys
}
