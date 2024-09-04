package baseapp

import (
	"context"
	"time"

	abci "github.com/cometbft/cometbft/abci/types"

	"cosmossdk.io/store/types"
)

type TxExecutor func(
	ctx context.Context,
	blockSize int,
	cms types.MultiStore,
	deliverTxWithMultiStore func(int, types.MultiStore, map[string]any) *abci.ExecTxResult,
	t time.Time, h int64,
) ([]*abci.ExecTxResult, error)
