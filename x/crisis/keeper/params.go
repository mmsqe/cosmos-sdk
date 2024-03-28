package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/errors"
	"github.com/cosmos/cosmos-sdk/x/crisis/types"
)

// GetConstantFee get's the constant fee from the store
func (k *Keeper) GetConstantFee(ctx sdk.Context) (constantFee sdk.Coin) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConstantFeeKey)
	if len(bz) == 0 {
		k.legacySubspace.GetIfExists(ctx, types.ParamStoreKeyConstantFee, &constantFee)
		return
	}
	k.cdc.MustUnmarshal(bz, &constantFee)
	return constantFee
}

// GetConstantFee set's the constant fee in the store
func (k *Keeper) SetConstantFee(ctx sdk.Context, constantFee sdk.Coin) error {
	if !constantFee.IsValid() || constantFee.IsNegative() {
		return errors.Wrapf(errors.ErrInvalidCoins, "negative or invalid constant fee: %s", constantFee)
	}

	store := ctx.KVStore(k.storeKey)
	bz, err := k.cdc.Marshal(&constantFee)
	if err != nil {
		return err
	}

	store.Set(types.ConstantFeeKey, bz)
	return nil
}
