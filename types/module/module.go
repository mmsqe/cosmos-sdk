/*
Package module contains application module patterns and associated "manager" functionality.
The module pattern has been broken down by:
  - independent module functionality (AppModuleBasic)
  - inter-dependent module genesis functionality (AppModuleGenesis)
  - inter-dependent module simulation functionality (AppModuleSimulation)
  - inter-dependent module full functionality (AppModule)

inter-dependent module functionality is module functionality which somehow
depends on other modules, typically through the module keeper.  Many of the
module keepers are dependent on each other, thus in order to access the full
set of module functionality we need to define all the keepers/params-store/keys
etc. This full set of advanced functionality is defined by the AppModule interface.

Independent module functions are separated to allow for the construction of the
basic application structures required early on in the application definition
and used to enable the definition of full module functionality later in the
process. This separation is necessary, however we still want to allow for a
high level pattern for modules to follow - for instance, such that we don't
have to manually register all of the codecs for all the modules. This basic
procedure as well as other basic patterns are handled through the use of
BasicManager.

Lastly the interface for genesis functionality (AppModuleGenesis) has been
separated out from full module functionality (AppModule) so that modules which
are only used for genesis can take advantage of the Module patterns without
needlessly defining many placeholder functions
*/
package module

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io/ioutil"
	"math"
	"os"
	"path/filepath"
	"sort"

	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"github.com/spf13/cobra"
	abci "github.com/tendermint/tendermint/abci/types"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/codec"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
)

// AppModuleBasic is the standard form for basic non-dependant elements of an application module.
type AppModuleBasic interface {
	Name() string
	RegisterLegacyAminoCodec(*codec.LegacyAmino)
	RegisterInterfaces(codectypes.InterfaceRegistry)

	DefaultGenesis(codec.JSONCodec) json.RawMessage
	ValidateGenesis(codec.JSONCodec, client.TxEncodingConfig, json.RawMessage) error

	// client functionality
	RegisterGRPCGatewayRoutes(client.Context, *runtime.ServeMux)
	GetTxCmd() *cobra.Command
	GetQueryCmd() *cobra.Command
}

// BasicManager is a collection of AppModuleBasic
type BasicManager map[string]AppModuleBasic

// NewBasicManager creates a new BasicManager object
func NewBasicManager(modules ...AppModuleBasic) BasicManager {
	moduleMap := make(map[string]AppModuleBasic)
	for _, module := range modules {
		moduleMap[module.Name()] = module
	}
	return moduleMap
}

// RegisterLegacyAminoCodec registers all module codecs
func (bm BasicManager) RegisterLegacyAminoCodec(cdc *codec.LegacyAmino) {
	for _, b := range bm {
		b.RegisterLegacyAminoCodec(cdc)
	}
}

// RegisterInterfaces registers all module interface types
func (bm BasicManager) RegisterInterfaces(registry codectypes.InterfaceRegistry) {
	for _, m := range bm {
		m.RegisterInterfaces(registry)
	}
}

// DefaultGenesis provides default genesis information for all modules
func (bm BasicManager) DefaultGenesis(cdc codec.JSONCodec) map[string]json.RawMessage {
	genesis := make(map[string]json.RawMessage)
	for _, b := range bm {
		genesis[b.Name()] = b.DefaultGenesis(cdc)
	}

	return genesis
}

// ValidateGenesis performs genesis state validation for all modules
func (bm BasicManager) ValidateGenesis(cdc codec.JSONCodec, txEncCfg client.TxEncodingConfig, genesis map[string]json.RawMessage) error {
	for _, b := range bm {
		if err := b.ValidateGenesis(cdc, txEncCfg, genesis[b.Name()]); err != nil {
			return err
		}
	}

	return nil
}

// RegisterGRPCGatewayRoutes registers all module rest routes
func (bm BasicManager) RegisterGRPCGatewayRoutes(clientCtx client.Context, rtr *runtime.ServeMux) {
	for _, b := range bm {
		b.RegisterGRPCGatewayRoutes(clientCtx, rtr)
	}
}

// AddTxCommands adds all tx commands to the rootTxCmd.
//
// TODO: Remove clientCtx argument.
// REF: https://github.com/cosmos/cosmos-sdk/issues/6571
func (bm BasicManager) AddTxCommands(rootTxCmd *cobra.Command) {
	for _, b := range bm {
		if cmd := b.GetTxCmd(); cmd != nil {
			rootTxCmd.AddCommand(cmd)
		}
	}
}

// AddQueryCommands adds all query commands to the rootQueryCmd.
//
// TODO: Remove clientCtx argument.
// REF: https://github.com/cosmos/cosmos-sdk/issues/6571
func (bm BasicManager) AddQueryCommands(rootQueryCmd *cobra.Command) {
	for _, b := range bm {
		if cmd := b.GetQueryCmd(); cmd != nil {
			rootQueryCmd.AddCommand(cmd)
		}
	}
}

// AppModuleGenesis is the standard form for an application module genesis functions
type AppModuleGenesis interface {
	AppModuleBasic

	InitGenesis(sdk.Context, codec.JSONCodec, json.RawMessage) []abci.ValidatorUpdate
	ExportGenesis(sdk.Context, codec.JSONCodec) json.RawMessage
}

// AppModule is the standard form for an application module
type AppModule interface {
	AppModuleGenesis

	// registers
	RegisterInvariants(sdk.InvariantRegistry)

	// RegisterServices allows a module to register services
	RegisterServices(Configurator)

	// ConsensusVersion is a sequence number for state-breaking change of the
	// module. It should be incremented on each consensus-breaking change
	// introduced by the module. To avoid wrong/empty versions, the initial version
	// should be set to 1.
	ConsensusVersion() uint64
}

// BeginBlockAppModule is an extension interface that contains information about the AppModule and BeginBlock.
type BeginBlockAppModule interface {
	AppModule
	BeginBlock(sdk.Context, abci.RequestBeginBlock)
}

// EndBlockAppModule is an extension interface that contains information about the AppModule and EndBlock.
type EndBlockAppModule interface {
	AppModule
	EndBlock(sdk.Context, abci.RequestEndBlock) []abci.ValidatorUpdate
}

// GenesisOnlyAppModule is an AppModule that only has import/export functionality
type GenesisOnlyAppModule struct {
	AppModuleGenesis
}

// NewGenesisOnlyAppModule creates a new GenesisOnlyAppModule object
func NewGenesisOnlyAppModule(amg AppModuleGenesis) AppModule {
	return GenesisOnlyAppModule{
		AppModuleGenesis: amg,
	}
}

// RegisterInvariants is a placeholder function register no invariants
func (GenesisOnlyAppModule) RegisterInvariants(_ sdk.InvariantRegistry) {}

// QuerierRoute returns an empty module querier route
func (GenesisOnlyAppModule) QuerierRoute() string { return "" }

// LegacyQuerierHandler returns an empty module querier
func (gam GenesisOnlyAppModule) LegacyQuerierHandler(*codec.LegacyAmino) sdk.Querier { return nil }

// RegisterServices registers all services.
func (gam GenesisOnlyAppModule) RegisterServices(Configurator) {}

// ConsensusVersion implements AppModule/ConsensusVersion.
func (gam GenesisOnlyAppModule) ConsensusVersion() uint64 { return 1 }

// BeginBlock returns an empty module begin-block
func (gam GenesisOnlyAppModule) BeginBlock(ctx sdk.Context, req abci.RequestBeginBlock) {}

// EndBlock returns an empty module end-block
func (GenesisOnlyAppModule) EndBlock(_ sdk.Context, _ abci.RequestEndBlock) []abci.ValidatorUpdate {
	return []abci.ValidatorUpdate{}
}

// Manager defines a module manager that provides the high level utility for managing and executing
// operations for a group of modules
type Manager struct {
	Modules            map[string]AppModule
	OrderInitGenesis   []string
	OrderExportGenesis []string
	OrderBeginBlockers []string
	OrderEndBlockers   []string
	OrderMigrations    []string
	GenesisPath        string
}

// NewManager creates a new Manager object
func NewManager(modules ...AppModule) *Manager {
	moduleMap := make(map[string]AppModule)
	modulesStr := make([]string, 0, len(modules))
	for _, module := range modules {
		moduleMap[module.Name()] = module
		modulesStr = append(modulesStr, module.Name())
	}

	return &Manager{
		Modules:            moduleMap,
		OrderInitGenesis:   modulesStr,
		OrderExportGenesis: modulesStr,
		OrderBeginBlockers: modulesStr,
		OrderEndBlockers:   modulesStr,
		GenesisPath:        "",
	}
}

// SetOrderInitGenesis sets the order of init genesis calls
func (m *Manager) SetOrderInitGenesis(moduleNames ...string) {
	m.assertNoForgottenModules("SetOrderInitGenesis", moduleNames)
	m.OrderInitGenesis = moduleNames
}

// SetOrderExportGenesis sets the order of export genesis calls
func (m *Manager) SetOrderExportGenesis(moduleNames ...string) {
	m.assertNoForgottenModules("SetOrderExportGenesis", moduleNames)
	m.OrderExportGenesis = moduleNames
}

// SetOrderBeginBlockers sets the order of set begin-blocker calls
func (m *Manager) SetOrderBeginBlockers(moduleNames ...string) {
	m.assertNoForgottenModules("SetOrderBeginBlockers", moduleNames)
	m.OrderBeginBlockers = moduleNames
}

// SetOrderEndBlockers sets the order of set end-blocker calls
func (m *Manager) SetOrderEndBlockers(moduleNames ...string) {
	m.assertNoForgottenModules("SetOrderEndBlockers", moduleNames)
	m.OrderEndBlockers = moduleNames
}

// SetOrderMigrations sets the order of migrations to be run. If not set
// then migrations will be run with an order defined in `DefaultMigrationsOrder`.
func (m *Manager) SetOrderMigrations(moduleNames ...string) {
	m.assertNoForgottenModules("SetOrderMigrations", moduleNames)
	m.OrderMigrations = moduleNames
}

// RegisterInvariants registers all module invariants
func (m *Manager) RegisterInvariants(ir sdk.InvariantRegistry) {
	for _, module := range m.Modules {
		module.RegisterInvariants(ir)
	}
}

// RegisterServices registers all module services
func (m *Manager) RegisterServices(cfg Configurator) {
	for _, module := range m.Modules {
		module.RegisterServices(cfg)
	}
}

// InitGenesis performs init genesis functionality for modules. Exactly one
// module must return a non-empty validator set update to correctly initialize
// the chain.
func (m *Manager) InitGenesis(ctx sdk.Context, cdc codec.JSONCodec, genesisData map[string]json.RawMessage) abci.ResponseInitChain {
	var validatorUpdates []abci.ValidatorUpdate
	ctx.Logger().Info("initializing blockchain state from genesis.json")
	initWithPath := (len(m.GenesisPath) != 0)
	for _, moduleName := range m.OrderInitGenesis {
		if (!initWithPath && genesisData[moduleName] == nil) ||
			(initWithPath && m.Modules[moduleName] == nil) {
			continue
		}
		ctx.Logger().Info("running initialization for module", "module", moduleName)

		var moduleValUpdates []abci.ValidatorUpdate
		if initWithPath {
			modulePath := filepath.Join(m.GenesisPath, moduleName)
			ctx.Logger().Info("loading module genesis state from", "path", modulePath)

			bz, err := FileRead(modulePath, moduleName)
			if err != nil {
				panic(fmt.Sprintf("failed to read the genesis state from file: %v", err))
			}

			moduleValUpdates = m.Modules[moduleName].InitGenesis(ctx, cdc, bz)
		} else {
			moduleValUpdates = m.Modules[moduleName].InitGenesis(ctx, cdc, genesisData[moduleName])
		}

		// use these validator updates if provided, the module manager assumes
		// only one module will update the validator set
		if len(moduleValUpdates) > 0 {
			if len(validatorUpdates) > 0 {
				panic("validator InitGenesis updates already set by a previous module")
			}
			validatorUpdates = moduleValUpdates
		}
	}

	// a chain must initialize with a non-empty validator set
	if len(validatorUpdates) == 0 {
		panic(fmt.Sprintf("validator set is empty after InitGenesis, please ensure at least one validator is initialized with a delegation greater than or equal to the DefaultPowerReduction (%d)", sdk.DefaultPowerReduction))
	}

	return abci.ResponseInitChain{
		Validators: validatorUpdates,
	}
}

// ExportGenesis performs export genesis functionality for modules
func (m *Manager) ExportGenesis(ctx sdk.Context, cdc codec.JSONCodec) (map[string]json.RawMessage, error) {
	genesisData := make(map[string]json.RawMessage)

	if len(m.GenesisPath) > 0 {
		for _, moduleName := range m.OrderExportGenesis {
			modulePath := filepath.Join(m.GenesisPath, moduleName)
			fmt.Printf("exporting module: %s,path: %s\n", moduleName, modulePath)

			bz := m.Modules[moduleName].ExportGenesis(ctx, cdc)
			if err := fileWrite(modulePath, moduleName, bz); err != nil {
				return nil, fmt.Errorf("ExportGenesis to file failed, module=%s err=%v", moduleName, err)
			}
		}
	} else {
		for _, moduleName := range m.OrderExportGenesis {
			genesisData[moduleName] = m.Modules[moduleName].ExportGenesis(ctx, cdc)
		}
	}

	return genesisData, nil
}

// assertNoForgottenModules checks that we didn't forget any modules in the
// SetOrder* functions.
func (m *Manager) assertNoForgottenModules(setOrderFnName string, moduleNames []string) {
	ms := make(map[string]bool)
	for _, m := range moduleNames {
		ms[m] = true
	}
	var missing []string
	for m := range m.Modules {
		if !ms[m] {
			missing = append(missing, m)
		}
	}
	if len(missing) != 0 {
		panic(fmt.Sprintf(
			"%s: all modules must be defined when setting %s, missing: %v", setOrderFnName, setOrderFnName, missing))
	}
}

// MigrationHandler is the migration function that each module registers.
type MigrationHandler func(sdk.Context) error

// VersionMap is a map of moduleName -> version
type VersionMap map[string]uint64

// RunMigrations performs in-place store migrations for all modules. This
// function MUST be called insde an x/upgrade UpgradeHandler.
//
// Recall that in an upgrade handler, the `fromVM` VersionMap is retrieved from
// x/upgrade's store, and the function needs to return the target VersionMap
// that will in turn be persisted to the x/upgrade's store. In general,
// returning RunMigrations should be enough:
//
// Example:
//
//	cfg := module.NewConfigurator(...)
//	app.UpgradeKeeper.SetUpgradeHandler("my-plan", func(ctx sdk.Context, plan upgradetypes.Plan, fromVM module.VersionMap) (module.VersionMap, error) {
//	    return app.mm.RunMigrations(ctx, cfg, fromVM)
//	})
//
// Internally, RunMigrations will perform the following steps:
// - create an `updatedVM` VersionMap of module with their latest ConsensusVersion
// - make a diff of `fromVM` and `udpatedVM`, and for each module:
//   - if the module's `fromVM` version is less than its `updatedVM` version,
//     then run in-place store migrations for that module between those versions.
//   - if the module does not exist in the `fromVM` (which means that it's a new module,
//     because it was not in the previous x/upgrade's store), then run
//     `InitGenesis` on that module.
//
// - return the `updatedVM` to be persisted in the x/upgrade's store.
//
// Migrations are run in an order defined by `Manager.OrderMigrations` or (if not set) defined by
// `DefaultMigrationsOrder` function.
//
// As an app developer, if you wish to skip running InitGenesis for your new
// module "foo", you need to manually pass a `fromVM` argument to this function
// foo's module version set to its latest ConsensusVersion. That way, the diff
// between the function's `fromVM` and `udpatedVM` will be empty, hence not
// running anything for foo.
//
// Example:
//
//	cfg := module.NewConfigurator(...)
//	app.UpgradeKeeper.SetUpgradeHandler("my-plan", func(ctx sdk.Context, plan upgradetypes.Plan, fromVM module.VersionMap) (module.VersionMap, error) {
//	    // Assume "foo" is a new module.
//	    // `fromVM` is fetched from existing x/upgrade store. Since foo didn't exist
//	    // before this upgrade, `v, exists := fromVM["foo"]; exists == false`, and RunMigration will by default
//	    // run InitGenesis on foo.
//	    // To skip running foo's InitGenesis, you need set `fromVM`'s foo to its latest
//	    // consensus version:
//	    fromVM["foo"] = foo.AppModule{}.ConsensusVersion()
//
//	    return app.mm.RunMigrations(ctx, cfg, fromVM)
//	})
//
// Please also refer to docs/core/upgrade.md for more information.
func (m Manager) RunMigrations(ctx sdk.Context, cfg Configurator, fromVM VersionMap) (VersionMap, error) {
	c, ok := cfg.(configurator)
	if !ok {
		return nil, sdkerrors.Wrapf(sdkerrors.ErrInvalidType, "expected %T, got %T", configurator{}, cfg)
	}
	modules := m.OrderMigrations
	if modules == nil {
		modules = DefaultMigrationsOrder(m.ModuleNames())
	}

	updatedVM := VersionMap{}
	for _, moduleName := range modules {
		module := m.Modules[moduleName]
		fromVersion, exists := fromVM[moduleName]
		toVersion := module.ConsensusVersion()

		// We run migration if the module is specified in `fromVM`.
		// Otherwise we run InitGenesis.
		//
		// The module won't exist in the fromVM in two cases:
		// 1. A new module is added. In this case we run InitGenesis with an
		// empty genesis state.
		// 2. An existing chain is upgrading from version < 0.43 to v0.43+ for the first time.
		// In this case, all modules have yet to be added to x/upgrade's VersionMap store.
		if exists {
			err := c.runModuleMigrations(ctx, moduleName, fromVersion, toVersion)
			if err != nil {
				return nil, err
			}
		} else {
			ctx.Logger().Info(fmt.Sprintf("adding a new module: %s", moduleName))
			moduleValUpdates := module.InitGenesis(ctx, c.cdc, module.DefaultGenesis(c.cdc))
			// The module manager assumes only one module will update the
			// validator set, and it can't be a new module.
			if len(moduleValUpdates) > 0 {
				return nil, sdkerrors.Wrapf(sdkerrors.ErrLogic, "validator InitGenesis update is already set by another module")
			}
		}

		updatedVM[moduleName] = toVersion
	}

	return updatedVM, nil
}

// BeginBlock performs begin block functionality for all modules. It creates a
// child context with an event manager to aggregate events emitted from all
// modules.
func (m *Manager) BeginBlock(ctx sdk.Context, req abci.RequestBeginBlock) abci.ResponseBeginBlock {
	ctx = ctx.WithEventManager(sdk.NewEventManager())

	for _, moduleName := range m.OrderBeginBlockers {
		module, ok := m.Modules[moduleName].(BeginBlockAppModule)
		if ok {
			module.BeginBlock(ctx, req)
		}
	}

	return abci.ResponseBeginBlock{
		Events: ctx.EventManager().ABCIEvents(),
	}
}

// EndBlock performs end block functionality for all modules. It creates a
// child context with an event manager to aggregate events emitted from all
// modules.
func (m *Manager) EndBlock(ctx sdk.Context, req abci.RequestEndBlock) abci.ResponseEndBlock {
	ctx = ctx.WithEventManager(sdk.NewEventManager())
	validatorUpdates := []abci.ValidatorUpdate{}

	for _, moduleName := range m.OrderEndBlockers {
		module, ok := m.Modules[moduleName].(EndBlockAppModule)
		if !ok {
			continue
		}
		moduleValUpdates := module.EndBlock(ctx, req)

		// use these validator updates if provided, the module manager assumes
		// only one module will update the validator set
		if len(moduleValUpdates) > 0 {
			if len(validatorUpdates) > 0 {
				panic("validator EndBlock updates already set by a previous module")
			}

			validatorUpdates = moduleValUpdates
		}
	}

	return abci.ResponseEndBlock{
		ValidatorUpdates: validatorUpdates,
		Events:           ctx.EventManager().ABCIEvents(),
	}
}

// GetVersionMap gets consensus version from all modules
func (m *Manager) GetVersionMap() VersionMap {
	vermap := make(VersionMap)
	for _, v := range m.Modules {
		version := v.ConsensusVersion()
		name := v.Name()
		vermap[name] = version
	}

	return vermap
}

// ModuleNames returns list of all module names, without any particular order.
func (m *Manager) ModuleNames() []string {
	ms := make([]string, len(m.Modules))
	i := 0
	for m := range m.Modules {
		ms[i] = m
		i++
	}
	return ms
}

// SetGenesisPath sets the genesis binaries export/import path.
func (m *Manager) SetGenesisPath(path string) {
	m.GenesisPath = path
}

// DefaultMigrationsOrder returns a default migrations order: ascending alphabetical by module name,
// except x/auth which will run last, see:
// https://github.com/cosmos/cosmos-sdk/issues/10591
func DefaultMigrationsOrder(modules []string) []string {
	const authName = "auth"
	out := make([]string, 0, len(modules))
	hasAuth := false
	for _, m := range modules {
		if m == authName {
			hasAuth = true
		} else {
			out = append(out, m)
		}
	}
	sort.Strings(out)
	if hasAuth {
		out = append(out, authName)
	}
	return out
}

func createExportFile(exportPath string, moduleName string, index int) (*os.File, error) {
	if err := os.MkdirAll(exportPath, 0o700); err != nil {
		return nil, fmt.Errorf("failed to create directory: %w", err)
	}

	fp := filepath.Join(exportPath, fmt.Sprintf("genesis_%s_%d.bin", moduleName, index))
	f, err := os.Create(fp)
	if err != nil {
		return nil, fmt.Errorf("failed to create file: %w", err)
	}

	return f, nil
}

func openModuleStateFile(importPath string, moduleName string, index int) (*os.File, error) {
	fp := filepath.Join(importPath, fmt.Sprintf("genesis_%s_%d.bin", moduleName, index))
	f, err := os.OpenFile(fp, os.O_RDONLY, 0o600)
	if err != nil {
		return nil, fmt.Errorf("failed to open file: %w", err)
	}

	return f, nil
}

const stateChunkSize = 100000000 // 100 MB

// byteChunk returns the chunk at a given index from the full byte slice.
func byteChunk(bz []byte, index int) []byte {
	start := index * stateChunkSize
	end := (index + 1) * stateChunkSize
	switch {
	case start >= len(bz):
		return nil
	case end >= len(bz):
		return bz[start:]
	default:
		return bz[start:end]
	}
}

// byteChunks calculates the number of chunks in the byte slice.
func byteChunks(bz []byte) int {
	return int(math.Ceil(float64(len(bz)) / float64(stateChunkSize)))
}

// fileWrite writes the module's genesis state into files, each file containing
// maximum 100 MB of data
func fileWrite(modulePath, moduleName string, bz []byte) error {
	chunks := byteChunks(bz)
	// if the genesis state is empty, still create a new file to write nothing
	if chunks == 0 {
		chunks++
	}
	totalWritten := 0
	for i := 0; i < chunks; i++ {
		f, err := createExportFile(modulePath, moduleName, i)
		if err != nil {
			return err
		}

		n, err := f.Write(byteChunk(bz, i))
		f.Close()
		if err != nil {
			return fmt.Errorf("failed to write genesis file: %w", err)
		}
		totalWritten += n
	}

	if totalWritten != len(bz) {
		return fmt.Errorf("genesis file was not fully written: written %d/ total %d", totalWritten, len(bz))
	}

	return nil
}

// FileRead reads the module's genesus state given the file path and the module name, returns json encoded
// data
func FileRead(modulePath string, moduleName string) ([]byte, error) {
	files, err := ioutil.ReadDir(modulePath)
	if err != nil {
		return nil, fmt.Errorf("failed to read folder from %s: %w", modulePath, err)
	}

	var buf bytes.Buffer
	for i := 0; i < len(files); i++ {
		f, err := openModuleStateFile(modulePath, moduleName, i)
		if err != nil {
			panic(fmt.Sprintf("failed to open genesis file from module %s: %v", moduleName, err))
		}
		if err = func() error {
			defer f.Close()

			fi, err := f.Stat()
			if err != nil {
				return fmt.Errorf("failed to stat file: %w", err)
			}

			n, err := buf.ReadFrom(f)
			if err != nil {
				return fmt.Errorf("failed to read file %s: %w", f.Name(), err)
			} else if n != fi.Size() {
				return fmt.Errorf("couldn't read entire file: %s, read: %d, file size: %d", f.Name(), n, fi.Size())
			}
			return nil
		}(); err != nil {
			return nil, err
		}
	}

	return buf.Bytes(), nil
}
