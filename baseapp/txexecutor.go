package baseapp

import (
	"context"
	"io"
	"sync/atomic"

	abci "github.com/cometbft/cometbft/abci/types"
	sdk "github.com/cosmos/cosmos-sdk/types"

	"cosmossdk.io/store/cachemulti"
	"cosmossdk.io/store/types"
	blockstm "github.com/crypto-org-chain/go-block-stm"
)

type TxResponsePatcher interface {
	Patch(input []*abci.ExecTxResult) []*abci.ExecTxResult
}

type stmMultiStoreWrapper struct {
	types.MultiStore
}

var _ blockstm.MultiStore = stmMultiStoreWrapper{}

func (ms stmMultiStoreWrapper) GetStore(key types.StoreKey) types.Store {
	return ms.MultiStore.GetStore(key)
}

func (ms stmMultiStoreWrapper) GetKVStore(key types.StoreKey) types.KVStore {
	return ms.MultiStore.GetKVStore(key)
}

func (ms stmMultiStoreWrapper) GetObjKVStore(key types.StoreKey) types.ObjKVStore {
	return ms.MultiStore.GetObjKVStore(key)
}

type msWrapper struct {
	blockstm.MultiStore
}

var _ types.MultiStore = msWrapper{}

func (ms msWrapper) getCacheWrapper(key types.StoreKey) types.CacheWrapper {
	return ms.GetStore(key)
}

func (ms msWrapper) GetStore(key types.StoreKey) types.Store {
	return ms.MultiStore.GetStore(key)
}

func (ms msWrapper) GetKVStore(key types.StoreKey) types.KVStore {
	return ms.MultiStore.GetKVStore(key)
}

func (ms msWrapper) GetObjKVStore(key types.StoreKey) types.ObjKVStore {
	return ms.MultiStore.GetObjKVStore(key)
}

func (ms msWrapper) CacheMultiStore() types.CacheMultiStore {
	return cachemulti.NewFromParent(ms.getCacheWrapper, nil, nil)
}

// Implements CacheWrapper.
func (ms msWrapper) CacheWrap() types.CacheWrap {
	return ms.CacheMultiStore().(types.CacheWrap)
}

// GetStoreType returns the type of the store.
func (ms msWrapper) GetStoreType() types.StoreType {
	return types.StoreTypeMulti
}

// Implements interface MultiStore
func (ms msWrapper) SetTracer(io.Writer) types.MultiStore {
	return nil
}

// Implements interface MultiStore
func (ms msWrapper) SetTracingContext(types.TraceContext) types.MultiStore {
	return nil
}

// Implements interface MultiStore
func (ms msWrapper) TracingEnabled() bool {
	return false
}

type TxExecutor func(
	ctx context.Context,
	block [][]byte,
	cms types.MultiStore,
	deliverTxWithMultiStore func(int, sdk.Tx, types.MultiStore, map[string]any) *abci.ExecTxResult,
	patcher TxResponsePatcher,
) ([]*abci.ExecTxResult, error)

func DefaultTxExecutor(_ context.Context,
	txs [][]byte,
	ms types.MultiStore,
	deliverTxWithMultiStore func(int, sdk.Tx, types.MultiStore, map[string]any) *abci.ExecTxResult,
	patcher TxResponsePatcher,
) ([]*abci.ExecTxResult, error) {
	blockSize := len(txs)
	results := make([]*abci.ExecTxResult, blockSize)
	for i := 0; i < blockSize; i++ {
		results[i] = deliverTxWithMultiStore(i, nil, ms, nil)
	}
	if patcher != nil {
		return patcher.Patch(results), nil
	}
	return nil, nil
}

func DefaultSTMTxExecutor(
	stores []types.StoreKey,
	workers int,
	txDecoder sdk.TxDecoder,
) TxExecutor {
	index := make(map[types.StoreKey]int, len(stores))
	for i, k := range stores {
		index[k] = i
	}
	return func(
		ctx context.Context,
		txs [][]byte,
		ms types.MultiStore,
		deliverTxWithMultiStore func(int, sdk.Tx, types.MultiStore, map[string]any) *abci.ExecTxResult,
		patcher TxResponsePatcher,
	) ([]*abci.ExecTxResult, error) {
		blockSize := len(txs)
		if blockSize == 0 {
			return nil, nil
		}
		results := make([]*abci.ExecTxResult, blockSize)
		incarnationCache := make([]atomic.Pointer[map[string]any], blockSize)
		for i := 0; i < blockSize; i++ {
			m := make(map[string]any)
			incarnationCache[i].Store(&m)
		}

		if err := blockstm.ExecuteBlock(
			ctx,
			blockSize,
			index,
			stmMultiStoreWrapper{ms},
			workers,
			func(txn blockstm.TxnIndex, ms blockstm.MultiStore) {
				var cache map[string]any
				// only one of the concurrent incarnations gets the cache if there are any, otherwise execute without
				// cache, concurrent incarnations should be rare.
				v := incarnationCache[txn].Swap(nil)
				if v != nil {
					cache = *v
				}
				results[txn] = deliverTxWithMultiStore(int(txn), nil, msWrapper{ms}, cache)

				if v != nil {
					incarnationCache[txn].Store(v)
				}
			},
		); err != nil {
			return nil, err
		}

		return patcher.Patch(results), nil
	}
}
