//go:build sims

package simapp

import (
	"encoding/binary"
	"encoding/json"
	"flag"
	"io"
	"math/rand"
	"sync"
	"testing"
	"time"

	abci "github.com/cometbft/cometbft/api/cometbft/abci/v1"
	cmtproto "github.com/cometbft/cometbft/api/cometbft/types/v1"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	corestore "cosmossdk.io/core/store"
	"cosmossdk.io/log"
	"cosmossdk.io/store"
	authzkeeper "cosmossdk.io/x/authz/keeper"
	"cosmossdk.io/x/feegrant"
	slashingtypes "cosmossdk.io/x/slashing/types"
	stakingtypes "cosmossdk.io/x/staking/types"

	"github.com/cosmos/cosmos-sdk/baseapp"
	servertypes "github.com/cosmos/cosmos-sdk/server/types"
	"github.com/cosmos/cosmos-sdk/simsx"
	simtestutil "github.com/cosmos/cosmos-sdk/testutil/sims"
	simtypes "github.com/cosmos/cosmos-sdk/types/simulation"
	"github.com/cosmos/cosmos-sdk/x/simulation"
	simcli "github.com/cosmos/cosmos-sdk/x/simulation/client/cli"
)

// SimAppChainID hardcoded chainID for simulation

var FlagEnableStreamingValue bool

// Get flags every time the simulator is run
func init() {
	simcli.GetSimulatorFlags()
	flag.BoolVar(&FlagEnableStreamingValue, "EnableStreaming", false, "Enable streaming service")
}

// interBlockCacheOpt returns a BaseApp option function that sets the persistent
// inter-block write-through cache.
func interBlockCacheOpt() func(*baseapp.BaseApp) {
	return baseapp.SetInterBlockCache(store.NewCommitKVStoreCacheManager())
}

func TestFullAppSimulation(t *testing.T) {
	simsx.Run(t, NewSimApp, setupStateFactory)
}

func setupStateFactory(app *SimApp) simsx.SimStateFactory {
	blockedAddre, _ := BlockedAddresses(app.interfaceRegistry.SigningContext().AddressCodec())
	return simsx.SimStateFactory{
		Codec:         app.AppCodec(),
		AppStateFn:    simtestutil.AppStateFn(app.AppCodec(), app.AuthKeeper.AddressCodec(), app.StakingKeeper.ValidatorAddressCodec(), app.SimulationManager().Modules, app.DefaultGenesis()),
		BlockedAddr:   blockedAddre,
		AccountSource: app.AuthKeeper,
		BalanceSource: app.BankKeeper,
	}
}

var (
	exportAllModules       []string
	exportWithValidatorSet []string
)

func TestAppImportExport(t *testing.T) {
	simsx.Run(t, NewSimApp, setupStateFactory, func(t testing.TB, ti simsx.TestInstance[*SimApp], _ []simtypes.Account) {
		app := ti.App
		t.Log("exporting genesis...\n")
		exported, err := app.ExportAppStateAndValidators(false, exportWithValidatorSet, exportAllModules)
		require.NoError(t, err)

		t.Log("importing genesis...\n")
		newTestInstance := simsx.NewSimulationAppInstance(t, ti.Cfg, NewSimApp)
		newApp := newTestInstance.App
		var genesisState GenesisState
		require.NoError(t, json.Unmarshal(exported.AppState, &genesisState))
		ctxB := newApp.NewContextLegacy(true, cmtproto.Header{Height: app.LastBlockHeight()})
		_, err = newApp.ModuleManager.InitGenesis(ctxB, genesisState)
		if IsEmptyValidatorSetErr(err) {
			t.Skip("Skipping simulation as all validators have been unbonded")
			return
		}
		require.NoError(t, err)
		err = newApp.StoreConsensusParams(ctxB, exported.ConsensusParams)
		require.NoError(t, err)

		t.Log("comparing stores...")
		// skip certain prefixes
		skipPrefixes := map[string][][]byte{
			stakingtypes.StoreKey: {
				stakingtypes.UnbondingQueueKey, stakingtypes.RedelegationQueueKey, stakingtypes.ValidatorQueueKey,
			},
			authzkeeper.StoreKey:   {authzkeeper.GrantQueuePrefix},
			feegrant.StoreKey:      {feegrant.FeeAllowanceQueueKeyPrefix},
			slashingtypes.StoreKey: {slashingtypes.ValidatorMissedBlockBitmapKeyPrefix},
		}
		AssertEqualStores(t, app, newApp, app.SimulationManager().StoreDecoders, skipPrefixes)
	})
}

// Scenario:
//
//	Start a fresh node and run n blocks, export state
//	set up a new node instance, Init chain from exported genesis
//	run new instance for n blocks
func TestAppSimulationAfterImport(t *testing.T) {
	simsx.Run(t, NewSimApp, setupStateFactory, func(t testing.TB, ti simsx.TestInstance[*SimApp], accs []simtypes.Account) {
		app := ti.App
		t.Log("exporting genesis...\n")
		exported, err := app.ExportAppStateAndValidators(false, exportWithValidatorSet, exportAllModules)
		require.NoError(t, err)

		importGenesisStateFactory := func(app *SimApp) simsx.SimStateFactory {
			return simsx.SimStateFactory{
				Codec: app.AppCodec(),
				AppStateFn: func(r *rand.Rand, _ []simtypes.Account, config simtypes.Config) (json.RawMessage, []simtypes.Account, string, time.Time) {
					t.Log("importing genesis...\n")
					genesisTimestamp := time.Unix(config.GenesisTime, 0)

					_, err = app.InitChain(&abci.InitChainRequest{
						AppStateBytes: exported.AppState,
						ChainId:       simsx.SimAppChainID,
						InitialHeight: exported.Height,
						Time:          genesisTimestamp,
					})
					if IsEmptyValidatorSetErr(err) {
						t.Skip("Skipping simulation as all validators have been unbonded")
						return nil, nil, "", time.Time{}
					}
					require.NoError(t, err)
					// use accounts from initial run
					return exported.AppState, accs, config.ChainID, genesisTimestamp
				},
				BlockedAddr:   must(BlockedAddresses(app.AuthKeeper.AddressCodec())),
				AccountSource: app.AuthKeeper,
				BalanceSource: app.BankKeeper,
			}
		}
		ti.Cfg.InitialBlockHeight = int(exported.Height)
		simsx.RunWithSeedAndRandAcc(t, ti.Cfg, NewSimApp, importGenesisStateFactory, ti.Cfg.Seed, ti.Cfg.FuzzSeed, simtypes.RandomAccounts)
	})
}

func TestAppStateDeterminism(t *testing.T) {
	const numTimesToRunPerSeed = 3
	var seeds []int64
	if s := simcli.NewConfigFromFlags().Seed; s != simcli.DefaultSeedValue {
		// We will be overriding the random seed and just run a single simulation on the provided seed value
		for j := 0; j < numTimesToRunPerSeed; j++ { // multiple rounds
			seeds = append(seeds, s)
		}
	} else {
		// setup with 3 random seeds
		for i := 0; i < 3; i++ {
			seed := rand.Int63()
			for j := 0; j < numTimesToRunPerSeed; j++ { // multiple rounds
				seeds = append(seeds, seed)
			}
		}
	}
	// overwrite default app config
	interBlockCachingAppFactory := func(logger log.Logger, db corestore.KVStoreWithBatch, traceStore io.Writer, loadLatest bool, appOpts servertypes.AppOptions, baseAppOptions ...func(*baseapp.BaseApp)) *SimApp {
		if FlagEnableStreamingValue {
			m := map[string]any{
				"streaming.abci.keys":             []string{"*"},
				"streaming.abci.plugin":           "abci_v1",
				"streaming.abci.stop-node-on-err": true,
			}
			others := appOpts
			appOpts = simsx.AppOptionsFn(func(k string) any {
				if v, ok := m[k]; ok {
					return v
				}
				return others.Get(k)
			})
		}
		return NewSimApp(logger, db, nil, true, appOpts, append(baseAppOptions, interBlockCacheOpt())...)
	}
	var mx sync.Mutex
	appHashResults := make(map[int64][][]byte)
	appSimLogger := make(map[int64][]simulation.LogWriter)
	captureAndCheckHash := func(t testing.TB, ti simsx.TestInstance[*SimApp], _ []simtypes.Account) {
		seed, appHash := ti.Cfg.Seed, ti.App.LastCommitID().Hash
		mx.Lock()
		otherHashes, execWriters := appHashResults[seed], appSimLogger[seed]
		if len(otherHashes) < numTimesToRunPerSeed-1 {
			appHashResults[seed], appSimLogger[seed] = append(otherHashes, appHash), append(execWriters, ti.ExecLogWriter)
		} else { // cleanup
			delete(appHashResults, seed)
			delete(appSimLogger, seed)
		}
		mx.Unlock()

		var failNow bool
		// and check that all app hashes per seed are equal for each iteration
		for i := 0; i < len(otherHashes); i++ {
			if !assert.Equal(t, otherHashes[i], appHash) {
				execWriters[i].PrintLogs()
				failNow = true
			}
		}
		if failNow {
			ti.ExecLogWriter.PrintLogs()
			t.Fatalf("non-determinism in seed %d", seed)
		}
	}
	// run simulations
	simsx.RunWithSeedsAndRandAcc(t, interBlockCachingAppFactory, setupStateFactory, seeds, []byte{}, simtypes.RandomAccounts, captureAndCheckHash)
}

func FuzzFullAppSimulation(f *testing.F) {
	f.Fuzz(func(t *testing.T, rawSeed []byte) {
		if len(rawSeed) < 8 {
			t.Skip()
			return
		}
		simsx.RunWithSeeds(
			t,
			NewSimApp,
			setupStateFactory,
			[]int64{int64(binary.BigEndian.Uint64(rawSeed))},
			rawSeed[8:],
		)
	})
}

func must[T any](r T, err error) T {
	if err != nil {
		panic(err)
	}
	return r
}
