package dbadapter

import (
	"io"

	"cosmossdk.io/store/cachekv"
	"cosmossdk.io/store/tracekv"
	"cosmossdk.io/store/types"
	dbm "github.com/cosmos/cosmos-db"
)

// DBStore is wrapper type for dbm.DB with implementation of KVStore
type DBStore struct {
	DB dbm.DB
}

// Get wraps the underlying DB's Get method panicking on error.
func (dsa DBStore) Get(key []byte) []byte {
	v, err := dsa.DB.Get(key)
	if err != nil {
		panic(err)
	}

	return v
}

// Has wraps the underlying DB's Has method panicking on error.
func (dsa DBStore) Has(key []byte) bool {
	ok, err := dsa.DB.Has(key)
	if err != nil {
		panic(err)
	}

	return ok
}

// Set wraps the underlying DB's Set method panicking on error.
func (dsa DBStore) Set(key, value []byte) {
	types.AssertValidKey(key)
	types.AssertValidValue(value)
	if err := dsa.DB.Set(key, value); err != nil {
		panic(err)
	}
}

// Delete wraps the underlying DB's Delete method panicking on error.
func (dsa DBStore) Delete(key []byte) {
	if err := dsa.DB.Delete(key); err != nil {
		panic(err)
	}
}

// Iterator wraps the underlying DB's Iterator method panicking on error.
func (dsa DBStore) Iterator(start, end []byte) types.Iterator {
	iter, err := dsa.DB.Iterator(start, end)
	if err != nil {
		panic(err)
	}

	return iter
}

// ReverseIterator wraps the underlying DB's ReverseIterator method panicking on error.
func (dsa DBStore) ReverseIterator(start, end []byte) types.Iterator {
	iter, err := dsa.DB.ReverseIterator(start, end)
	if err != nil {
		panic(err)
	}

	return iter
}

// GetStoreType returns the type of the store.
func (DBStore) GetStoreType() types.StoreType {
	return types.StoreTypeDB
}

// CacheWrap branches the underlying store.
func (dsa DBStore) CacheWrap() types.CacheWrap {
	return cachekv.NewStore(dsa)
}

// CacheWrapWithTrace implements KVStore.
func (dsa DBStore) CacheWrapWithTrace(w io.Writer, tc types.TraceContext) types.CacheWrap {
	return cachekv.NewStore(tracekv.NewStore(dsa, w, tc))
}

// dbm.DB implements KVStore so we can CacheKVStore it.
var _ types.KVStore = DBStore{}
