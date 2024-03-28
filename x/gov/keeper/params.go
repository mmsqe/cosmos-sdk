package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/x/gov/types"
	v1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
)

// SetParams sets the gov module's parameters.
func (k Keeper) SetParams(ctx sdk.Context, params v1.Params) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := k.cdc.Marshal(&params)
	if err != nil {
		return err
	}
	store.Set(types.ParamsKey, bz)

	return nil
}

// GetParams gets the gov module's parameters.
func (k Keeper) GetParams(clientCtx sdk.Context) (params v1.Params) {
	store := clientCtx.KVStore(k.storeKey)
	bz := store.Get(types.ParamsKey)
	if len(bz) == 0 {
		var depositParams v1.DepositParams
		k.legacySubspace.Get(clientCtx, v1.ParamStoreKeyDepositParams, &depositParams)
		var votingParams v1.VotingParams
		k.legacySubspace.Get(clientCtx, v1.ParamStoreKeyVotingParams, &votingParams)
		var tallyParams v1.TallyParams
		k.legacySubspace.Get(clientCtx, v1.ParamStoreKeyTallyParams, &tallyParams)
		params = v1.Params{
			MinDeposit:       depositParams.MinDeposit,
			MaxDepositPeriod: depositParams.MaxDepositPeriod,
			VotingPeriod:     votingParams.VotingPeriod,
			Quorum:           tallyParams.Quorum,
			Threshold:        tallyParams.Threshold,
			VetoThreshold:    tallyParams.VetoThreshold,
		}
		return params
	}

	k.cdc.MustUnmarshal(bz, &params)
	return params
}
