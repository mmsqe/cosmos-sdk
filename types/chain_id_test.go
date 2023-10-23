package types_test

import (
	strings "strings"
	"testing"

	sdktypes "github.com/cosmos/cosmos-sdk/types"
	genutiltypes "github.com/cosmos/cosmos-sdk/x/genutil/types"
	"github.com/stretchr/testify/require"
)

func TestParseChainIDFromGenesis(t *testing.T) {
	testCases := []struct {
		name       string
		json       string
		expChainID string
	}{
		{
			"success",
			`{
				"state": {
				  "accounts": {
					  "a": {}
				  }
				},
				"chain_id": "test-chain-id"
			}`,
			"test-chain-id",
		},
		{
			"not exist",
			`{
				"state": {
				  "accounts": {
					"a": {}
				  }
				},
				"chain-id": "test-chain-id"
			}`,
			"",
		},
		{
			"invalid type",
			`{
				"chain-id":1,
			}`,
			"",
		},
		{
			"invalid json",
			`[ " ': }`,
			"",
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			chain_id, err := sdktypes.ParseChainIDFromGenesis(strings.NewReader(tc.json))
			if tc.expChainID == "" {
				require.Error(t, err)
			} else {
				require.NoError(t, err)
				require.Equal(t, tc.expChainID, chain_id)
			}
		})
	}
}

func BenchmarkParseChainID(b *testing.B) {
	// an arbitrary genesis file from a cronos devnet.
	json := `
{
  "genesis_time": "2023-09-27T05:35:43.213433Z",
  "chain_id": "cronos_777-1",
  "initial_height": "1",
  "consensus_params": {
    "block": {
      "max_bytes": "1048576",
      "max_gas": "81500000"
    },
    "evidence": {
      "max_age_num_blocks": "100000",
      "max_age_duration": "172800000000000",
      "max_bytes": "1048576"
    },
    "validator": {
      "pub_key_types": [
        "ed25519"
      ]
    },
    "version": {
      "app": "0"
    }
  },
  "app_hash": "",
  "app_state": {
    "07-tendermint": null,
    "auth": {
      "params": {
        "max_memo_characters": "256",
        "tx_sig_limit": "7",
        "tx_size_cost_per_byte": "10",
        "sig_verify_cost_ed25519": "590",
        "sig_verify_cost_secp256k1": "1000"
      },
      "accounts": [
        {
          "@type": "/ethermint.types.v1.EthAccount",
          "base_account": {
            "address": "crc12luku6uxehhak02py4rcz65zu0swh7wjsrw0pp",
            "pub_key": null,
            "account_number": "0",
            "sequence": "0"
          },
          "code_hash": "0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
        },
        {
          "@type": "/ethermint.types.v1.EthAccount",
          "base_account": {
            "address": "crc18z6q38mhvtsvyr5mak8fj8s8g4gw7kjjtsgrn7",
            "pub_key": null,
            "account_number": "1",
            "sequence": "0"
          },
          "code_hash": "0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
        },
        {
          "@type": "/ethermint.types.v1.EthAccount",
          "base_account": {
            "address": "crc1x7x9pkfxf33l87ftspk5aetwnkr0lvlv3346cd",
            "pub_key": null,
            "account_number": "2",
            "sequence": "0"
          },
          "code_hash": "0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
        },
        {
          "@type": "/ethermint.types.v1.EthAccount",
          "base_account": {
            "address": "crc16z0herz998946wr659lr84c8c556da55dc34hh",
            "pub_key": null,
            "account_number": "3",
            "sequence": "0"
          },
          "code_hash": "0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
        },
        {
          "@type": "/ethermint.types.v1.EthAccount",
          "base_account": {
            "address": "crc1q04jewhxw4xxu3vlg3rc85240h9q7ns6hglz0g",
            "pub_key": null,
            "account_number": "4",
            "sequence": "0"
          },
          "code_hash": "0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
        }
      ]
    },
    "authz": {
      "authorization": []
    },
    "bank": {
      "params": {
        "send_enabled": [],
        "default_send_enabled": true
      },
      "balances": [
        {
          "address": "crc1q04jewhxw4xxu3vlg3rc85240h9q7ns6hglz0g",
          "coins": [
            {
              "denom": "basetcro",
              "amount": "30000000000000000000000"
            }
          ]
        },
        {
          "address": "crc1x7x9pkfxf33l87ftspk5aetwnkr0lvlv3346cd",
          "coins": [
            {
              "denom": "basetcro",
              "amount": "10000000000000000000000"
            }
          ]
        },
        {
          "address": "crc18z6q38mhvtsvyr5mak8fj8s8g4gw7kjjtsgrn7",
          "coins": [
            {
              "denom": "basetcro",
              "amount": "10000000000000000000000"
            },
            {
              "denom": "stake",
              "amount": "1000000000000000000"
            }
          ]
        },
        {
          "address": "crc12luku6uxehhak02py4rcz65zu0swh7wjsrw0pp",
          "coins": [
            {
              "denom": "basetcro",
              "amount": "10000000000000000000000"
            },
            {
              "denom": "stake",
              "amount": "1000000000000000000"
            }
          ]
        },
        {
          "address": "crc16z0herz998946wr659lr84c8c556da55dc34hh",
          "coins": [
            {
              "denom": "basetcro",
              "amount": "20000000000000000000000"
            }
          ]
        }
      ],
      "supply": [
        {
          "denom": "basetcro",
          "amount": "80000000000000000000000"
        },
        {
          "denom": "stake",
          "amount": "2000000000000000000"
        }
      ],
      "denom_metadata": [],
      "send_enabled": []
    },
    "capability": {
      "index": "1",
      "owners": []
    },
    "consensus": null,
    "crisis": {
      "constant_fee": {
        "denom": "stake",
        "amount": "1000"
      }
    },
    "cronos": {
      "params": {
        "ibc_cro_denom": "ibc/6411AE2ADA1E73DB59DB151A8988F9B7D5E7E233D8414DB6817F8F1A01611F86",
        "ibc_timeout": "86400000000000",
        "cronos_admin": "crc12luku6uxehhak02py4rcz65zu0swh7wjsrw0pp",
        "enable_auto_deployment": true
      },
      "external_contracts": [],
      "auto_contracts": []
    },
    "distribution": {
      "params": {
        "community_tax": "0.020000000000000000",
        "base_proposer_reward": "0.000000000000000000",
        "bonus_proposer_reward": "0.000000000000000000",
        "withdraw_addr_enabled": true
      },
      "fee_pool": {
        "community_pool": []
      },
      "delegator_withdraw_infos": [],
      "previous_proposer": "",
      "outstanding_rewards": [],
      "validator_accumulated_commissions": [],
      "validator_historical_rewards": [],
      "validator_current_rewards": [],
      "delegator_starting_infos": [],
      "validator_slash_events": []
    },
    "evidence": {
      "evidence": []
    },
    "evm": {
      "accounts": [],
      "params": {
        "evm_denom": "basetcro",
        "enable_create": true,
        "enable_call": true,
        "extra_eips": [],
        "chain_config": {
          "homestead_block": "0",
          "dao_fork_block": "0",
          "dao_fork_support": true,
          "eip150_block": "0",
          "eip150_hash": "0x0000000000000000000000000000000000000000000000000000000000000000",
          "eip155_block": "0",
          "eip158_block": "0",
          "byzantium_block": "0",
          "constantinople_block": "0",
          "petersburg_block": "0",
          "istanbul_block": "0",
          "muir_glacier_block": "0",
          "berlin_block": "0",
          "london_block": "0",
          "arrow_glacier_block": "0",
          "gray_glacier_block": "0",
          "merge_netsplit_block": "0",
          "shanghai_block": "0",
          "cancun_block": "0"
        },
        "allow_unprotected_txs": false
      }
    },
    "feegrant": {
      "allowances": []
    },
    "feeibc": {
      "identified_fees": [],
      "fee_enabled_channels": [],
      "registered_payees": [],
      "registered_counterparty_payees": [],
      "forward_relayers": []
    },
    "feemarket": {
      "params": {
        "no_base_fee": false,
        "base_fee_change_denominator": 8,
        "elasticity_multiplier": 2,
        "enable_height": "0",
        "base_fee": "100000000000",
        "min_gas_price": "0.000000000000000000",
        "min_gas_multiplier": "0.500000000000000000"
      },
      "block_gas": "0"
    },
    "genutil": {
      "gen_txs": [
        {
          "body": {
            "messages": [
              {
                "@type": "/cosmos.staking.v1beta1.MsgCreateValidator",
                "description": {
                  "moniker": "node1",
                  "identity": "",
                  "website": "",
                  "security_contact": "",
                  "details": ""
                },
                "commission": {
                  "rate": "0.100000000000000000",
                  "max_rate": "0.200000000000000000",
                  "max_change_rate": "0.010000000000000000"
                },
                "min_self_delegation": "1",
                "delegator_address": "crc18z6q38mhvtsvyr5mak8fj8s8g4gw7kjjtsgrn7",
                "validator_address": "crcvaloper18z6q38mhvtsvyr5mak8fj8s8g4gw7kjjp0e0dh",
                "pubkey": {
                  "@type": "/cosmos.crypto.ed25519.PubKey",
                  "key": "VYjUEP/dlIS1m5QVwzw4TwpGFXIbHwX+nXl0EilxXss="
                },
                "value": {
                  "denom": "stake",
                  "amount": "1000000000000000000"
                }
              }
            ],
            "memo": "03116e1d4dc9b09cdae5ae2b6a9512e37d1e000f@192.168.0.8:26656",
            "timeout_height": "0",
            "extension_options": [],
            "non_critical_extension_options": []
          },
          "auth_info": {
            "signer_infos": [
              {
                "public_key": {
                  "@type": "/ethermint.crypto.v1.ethsecp256k1.PubKey",
                  "key": "AkJ4WnUHRFLWKmrCInD/uPsByTddC6coh66ADcYZMV0b"
                },
                "mode_info": {
                  "single": {
                    "mode": "SIGN_MODE_DIRECT"
                  }
                },
                "sequence": "0"
              }
            ],
            "fee": {
              "amount": [],
              "gas_limit": "200000",
              "payer": "",
              "granter": ""
            },
            "tip": null
          },
          "signatures": [
            "vXMjRJSsXYoNEDnWKwu6P/O3PcaOAcLcbNmPraP5e1Euk7bE+0/2IiFAJV7iQsHuQYKA3lzS4Wtq9nmmjwXzYQE="
          ]
        },
        {
          "body": {
            "messages": [
              {
                "@type": "/cosmos.staking.v1beta1.MsgCreateValidator",
                "description": {
                  "moniker": "node0",
                  "identity": "",
                  "website": "",
                  "security_contact": "",
                  "details": ""
                },
                "commission": {
                  "rate": "0.100000000000000000",
                  "max_rate": "0.200000000000000000",
                  "max_change_rate": "0.010000000000000000"
                },
                "min_self_delegation": "1",
                "delegator_address": "crc12luku6uxehhak02py4rcz65zu0swh7wjsrw0pp",
                "validator_address": "crcvaloper12luku6uxehhak02py4rcz65zu0swh7wj6ulrlg",
                "pubkey": {
                  "@type": "/cosmos.crypto.ed25519.PubKey",
                  "key": "XMFekpj1jUgxm8jx4PRiDGk8tqqmdPYEVBrHdk122Pw="
                },
                "value": {
                  "denom": "stake",
                  "amount": "1000000000000000000"
                }
              }
            ],
            "memo": "6bdd363882d10473b99c8c710661f79d38bd5ce6@192.168.0.8:26656",
            "timeout_height": "0",
            "extension_options": [],
            "non_critical_extension_options": []
          },
          "auth_info": {
            "signer_infos": [
              {
                "public_key": {
                  "@type": "/ethermint.crypto.v1.ethsecp256k1.PubKey",
                  "key": "Am5xCmKjQt4O1NfEUy3Ly7r78ZZS7WeyN++rcOiyB++s"
                },
                "mode_info": {
                  "single": {
                    "mode": "SIGN_MODE_DIRECT"
                  }
                },
                "sequence": "0"
              }
            ],
            "fee": {
              "amount": [],
              "gas_limit": "200000",
              "payer": "",
              "granter": ""
            },
            "tip": null
          },
          "signatures": [
            "xiDZO94CFnydjTKevKRg/lpDSAK0LO/nxrcdJRjnvaZA3znfV+YUwqBPr9GU+Jcxi+QBUg+Rp3JLq1HJR/it+gA="
          ]
        }
      ]
    },
    "gov": {
      "starting_proposal_id": "1",
      "deposits": [],
      "votes": [],
      "proposals": [],
      "deposit_params": null,
      "voting_params": null,
      "tally_params": null,
      "params": {
        "min_deposit": [
          {
            "amount": "1",
            "denom": "basetcro"
          }
        ],
        "max_deposit_period": "10s",
        "voting_period": "10s",
        "quorum": "0.334000000000000000",
        "threshold": "0.500000000000000000",
        "veto_threshold": "0.334000000000000000",
        "min_initial_deposit_ratio": "0.000000000000000000",
        "burn_vote_quorum": false,
        "burn_proposal_deposit_prevote": false,
        "burn_vote_veto": true
      }
    },
    "gravity": {
      "params": {
        "gravity_id": "defaultgravityid",
        "contract_source_hash": "",
        "bridge_ethereum_address": "0x0000000000000000000000000000000000000000",
        "bridge_chain_id": "0",
        "signed_signer_set_txs_window": "10000",
        "signed_batches_window": "10000",
        "ethereum_signatures_window": "10000",
        "target_eth_tx_timeout": "43200000",
        "average_block_time": "5000",
        "average_ethereum_block_time": "15000",
        "slash_fraction_signer_set_tx": "0.001000000000000000",
        "slash_fraction_batch": "0.001000000000000000",
        "slash_fraction_ethereum_signature": "0.001000000000000000",
        "slash_fraction_conflicting_ethereum_signature": "0.001000000000000000",
        "unbond_slashing_signer_set_txs_window": "10000",
        "bridge_active": true,
        "batch_creation_period": "10",
        "batch_max_element": "100",
        "observe_ethereum_height_period": "50"
      },
      "last_observed_event_nonce": "0",
      "outgoing_txs": [],
      "confirmations": [],
      "ethereum_event_vote_records": [],
      "delegate_keys": [],
      "erc20_to_denoms": [],
      "unbatched_send_to_ethereum_txs": []
    },
    "ibc": {
      "client_genesis": {
        "clients": [],
        "clients_consensus": [],
        "clients_metadata": [],
        "params": {
          "allowed_clients": [
            "06-solomachine",
            "07-tendermint",
            "09-localhost"
          ]
        },
        "create_localhost": false,
        "next_client_sequence": "0"
      },
      "connection_genesis": {
        "connections": [],
        "client_connection_paths": [],
        "next_connection_sequence": "0",
        "params": {
          "max_expected_time_per_block": "30000000000"
        }
      },
      "channel_genesis": {
        "channels": [],
        "acknowledgements": [],
        "commitments": [],
        "receipts": [],
        "send_sequences": [],
        "recv_sequences": [],
        "ack_sequences": [],
        "next_channel_sequence": "0"
      }
    },
    "icaauth": {
      "params": {
        "min_timeout_duration": "3600s"
      }
    },
    "interchainaccounts": {
      "controller_genesis_state": {
        "active_channels": [],
        "interchain_accounts": [],
        "ports": [],
        "params": {
          "controller_enabled": true
        }
      },
      "host_genesis_state": {
        "active_channels": [],
        "interchain_accounts": [],
        "port": "icahost",
        "params": {
          "host_enabled": true,
          "allow_messages": [
            "*"
          ]
        }
      }
    },
    "mint": {
      "minter": {
        "inflation": "0.130000000000000000",
        "annual_provisions": "0.000000000000000000"
      },
      "params": {
        "mint_denom": "stake",
        "inflation_rate_change": "0.130000000000000000",
        "inflation_max": "0.200000000000000000",
        "inflation_min": "0.070000000000000000",
        "goal_bonded": "0.670000000000000000",
        "blocks_per_year": "6311520"
      }
    },
    "params": null,
    "slashing": {
      "params": {
        "signed_blocks_window": "100",
        "min_signed_per_window": "0.500000000000000000",
        "downtime_jail_duration": "600s",
        "slash_fraction_double_sign": "0.050000000000000000",
        "slash_fraction_downtime": "0.010000000000000000"
      },
      "signing_infos": [],
      "missed_blocks": []
    },
    "staking": {
      "params": {
        "unbonding_time": "1814400s",
        "max_validators": 100,
        "max_entries": 7,
        "historical_entries": 10000,
        "bond_denom": "stake",
        "min_commission_rate": "0.000000000000000000"
      },
      "last_total_power": "0",
      "last_validator_powers": [],
      "validators": [],
      "delegations": [],
      "unbonding_delegations": [],
      "redelegations": [],
      "exported": false
    },
    "transfer": {
      "port_id": "transfer",
      "denom_traces": [],
      "params": {
        "send_enabled": true,
        "receive_enabled": true
      },
      "total_escrowed": []
    },
    "upgrade": {},
    "vesting": {}
  }
}
`
	b.Run("new", func(b *testing.B) {
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			_, err := sdktypes.ParseChainIDFromGenesis(strings.NewReader(json))
			require.NoError(b, err)
		}
	})

	b.Run("old", func(b *testing.B) {
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			_, err := genutiltypes.AppGenesisFromReader(strings.NewReader(json))
			require.NoError(b, err)
		}
	})
}
