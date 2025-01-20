package runtime

import (
	"fmt"

	"cosmossdk.io/core/server"
	"cosmossdk.io/depinject"
)

// ModuleConfigMaps is a map module scoped ConfigMaps
type ModuleConfigMaps map[string]server.ConfigMap

type ModuleConfigMapsInput struct {
	depinject.In

	ModuleConfigs []server.ModuleConfigMap
	DynamicConfig server.DynamicConfig `optional:"true"`
}

// ProvideModuleConfigMaps returns a map of module name to module config map.
// The module config map is a map of flag to value.
func ProvideModuleConfigMaps(in ModuleConfigMapsInput) ModuleConfigMaps {
	moduleConfigMaps := make(ModuleConfigMaps)
	fmt.Println("mm-ProvideModuleConfigMaps", in.DynamicConfig == nil)
	if in.DynamicConfig == nil {
		return moduleConfigMaps
	}
	for _, moduleConfig := range in.ModuleConfigs {
		cfg := moduleConfig.Config
		name := moduleConfig.Module
		moduleConfigMaps[name] = make(server.ConfigMap)
		for flag, df := range cfg {
			val := in.DynamicConfig.Get(flag)
			if val != nil {
				moduleConfigMaps[name][flag] = val
			} else {
				moduleConfigMaps[name][flag] = df
			}
		}
	}
	fmt.Println("mm-ProvideModuleConfigMaps", moduleConfigMaps)
	return moduleConfigMaps
}

func ProvideModuleScopedConfigMap(
	key depinject.ModuleKey,
	moduleConfigs ModuleConfigMaps,
) server.ConfigMap {
	fmt.Println("mm-ProvideModuleScopedConfigMap", key)
	return moduleConfigs[key.Name()]
}
