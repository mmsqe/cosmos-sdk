package types_test

import (
	_ "embed"
	"errors"
	fmt "fmt"
	"strings"
	"testing"

	"github.com/cosmos/cosmos-sdk/types"
	genutiltypes "github.com/cosmos/cosmos-sdk/x/genutil/types"
	"github.com/creachadair/jtree"
	"github.com/stretchr/testify/require"
)

//go:embed testdata/parse_chain_id.json
var BenchmarkGenesis string

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
			"nested",
			`{
				"state": {
				  "accounts": {
					"a": {}
				  },
				  "chain_id": "test-chain-id"
				}
			}`,
			"",
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
		{
			"empty chain_id",
			`{"chain_id": ""}`,
			"",
		},
		{
			"chain_id too long",
			`{"chain_id": "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"}`,
			"",
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			chain_id, err := types.ParseChainIDFromGenesis(strings.NewReader(tc.json))
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
	b.ReportAllocs()
	b.Run("new", func(b *testing.B) {
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			chainId, err := types.ParseChainIDFromGenesis(strings.NewReader(BenchmarkGenesis))
			require.NoError(b, err)
			require.Equal(b, "test_777-1", chainId)
		}
	})

	b.Run("old", func(b *testing.B) {
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			doc, err := genutiltypes.AppGenesisFromReader(strings.NewReader(BenchmarkGenesis))
			require.NoError(b, err)
			require.Equal(b, "test_777-1", doc.ChainID)
		}
	})

	b.Run("jstream", func(b *testing.B) {
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			chainId, err := types.ParseChainIDFromGenesisJstream(strings.NewReader(BenchmarkGenesis))
			require.NoError(b, err)
			require.Equal(b, "test_777-1", chainId)
		}
	})

	b.Run("jtree", func(b *testing.B) {
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			st := jtree.NewStream(strings.NewReader(BenchmarkGenesis))
			termErr := errors.New("value found")
			th := &testHandler{
				TargetKey:      "chain_id",
				TerminateError: termErr,
			}
			if err := st.Parse(th); err != nil {
				if err != termErr {
					b.Errorf("Parse failed: %v", err)
				}
			}
			require.Equal(b, "\"test_777-1\"", string(th.GetTargetValue()))
		}
	})
}

type testHandler struct {
	TargetKey      string
	TerminateError error
	targetValue    []byte
	keyFound       bool
}

func (t *testHandler) GetTargetValue() []byte {
	return t.targetValue
}

func (t *testHandler) BeginObject(loc jtree.Anchor) error { return nil }
func (t *testHandler) EndObject(loc jtree.Anchor) error   { return nil }
func (t *testHandler) BeginArray(loc jtree.Anchor) error  { return nil }
func (t *testHandler) EndArray(loc jtree.Anchor) error    { return nil }
func (t *testHandler) EndOfInput(loc jtree.Anchor)        {}

func (t *testHandler) BeginMember(loc jtree.Anchor) error {
	if string(loc.Text()) == fmt.Sprintf(`"%s"`, t.TargetKey) {
		t.keyFound = true
	}
	return nil
}

func (t *testHandler) EndMember(loc jtree.Anchor) error {
	return nil
}

func (t *testHandler) Value(loc jtree.Anchor) error {
	if t.keyFound {
		t.targetValue = loc.Text()
		return t.TerminateError
	}
	return nil
}

func (t *testHandler) SyntaxError(loc jtree.Anchor, err error) error {
	return err
}
