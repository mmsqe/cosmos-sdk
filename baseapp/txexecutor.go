package baseapp

import (
	"context"

	abci "github.com/cometbft/cometbft/abci/types"
	sdk "github.com/cosmos/cosmos-sdk/types"

	"cosmossdk.io/store/types"
)

type TxResponsePatcher interface {
	Patch(input []*abci.ExecTxResult) []*abci.ExecTxResult
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
