package types

import (
	"encoding/json"
	"errors"
	"io"
)

const ChainIDFieldName = "chain_id"

// ParseChainIDFromGenesis parses the chain-id from the genesis file using constant memory.
func ParseChainIDFromGenesis(r io.Reader) (string, error) {
	dec := json.NewDecoder(r)

	var t json.Token
	t, err := dec.Token()
	if err != nil {
		return "", err
	}
	if delim, ok := t.(json.Delim); !ok || delim != '{' {
		return "", errors.New("invalid delim: " + string(delim))
	}

	for dec.More() {
		t, err = dec.Token()
		if err != nil {
			return "", err
		}
		var obj interface{}
		err = dec.Decode(&obj)
		if err != nil {
			return "", err
		}
		if t == "chain_id" {
			return obj.(string), nil
		}
	}
	return "", errors.New("chain-id not found in genesis file")
}
