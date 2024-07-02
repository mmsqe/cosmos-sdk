// Code generated by MockGen. DO NOT EDIT.
// Source: baseapp/abci_utils.go

// Package mock is a generated GoMock package.
package mock

import (
	context "context"
	reflect "reflect"

	crypto "github.com/cometbft/cometbft/proto/tendermint/crypto"
	types "github.com/cosmos/cosmos-sdk/types"
	gomock "github.com/golang/mock/gomock"
)

// MockValidatorStore is a mock of ValidatorStore interface.
type MockValidatorStore struct {
	ctrl     *gomock.Controller
	recorder *MockValidatorStoreMockRecorder
}

// MockValidatorStoreMockRecorder is the mock recorder for MockValidatorStore.
type MockValidatorStoreMockRecorder struct {
	mock *MockValidatorStore
}

// NewMockValidatorStore creates a new mock instance.
func NewMockValidatorStore(ctrl *gomock.Controller) *MockValidatorStore {
	mock := &MockValidatorStore{ctrl: ctrl}
	mock.recorder = &MockValidatorStoreMockRecorder{mock}
	return mock
}

// EXPECT returns an object that allows the caller to indicate expected use.
func (m *MockValidatorStore) EXPECT() *MockValidatorStoreMockRecorder {
	return m.recorder
}

// GetPubKeyByConsAddr mocks base method.
func (m *MockValidatorStore) GetPubKeyByConsAddr(arg0 context.Context, arg1 types.ConsAddress) (crypto.PublicKey, error) {
	m.ctrl.T.Helper()
	ret := m.ctrl.Call(m, "GetPubKeyByConsAddr", arg0, arg1)
	ret0, _ := ret[0].(crypto.PublicKey)
	ret1, _ := ret[1].(error)
	return ret0, ret1
}

// GetPubKeyByConsAddr indicates an expected call of GetPubKeyByConsAddr.
func (mr *MockValidatorStoreMockRecorder) GetPubKeyByConsAddr(arg0, arg1 interface{}) *gomock.Call {
	mr.mock.ctrl.T.Helper()
	return mr.mock.ctrl.RecordCallWithMethodType(mr.mock, "GetPubKeyByConsAddr", reflect.TypeOf((*MockValidatorStore)(nil).GetPubKeyByConsAddr), arg0, arg1)
}

// MockGasTx is a mock of GasTx interface.
type MockGasTx struct {
	ctrl     *gomock.Controller
	recorder *MockGasTxMockRecorder
}

// MockGasTxMockRecorder is the mock recorder for MockGasTx.
type MockGasTxMockRecorder struct {
	mock *MockGasTx
}

// NewMockGasTx creates a new mock instance.
func NewMockGasTx(ctrl *gomock.Controller) *MockGasTx {
	mock := &MockGasTx{ctrl: ctrl}
	mock.recorder = &MockGasTxMockRecorder{mock}
	return mock
}

// EXPECT returns an object that allows the caller to indicate expected use.
func (m *MockGasTx) EXPECT() *MockGasTxMockRecorder {
	return m.recorder
}

// GetGas mocks base method.
func (m *MockGasTx) GetGas() uint64 {
	m.ctrl.T.Helper()
	ret := m.ctrl.Call(m, "GetGas")
	ret0, _ := ret[0].(uint64)
	return ret0
}

// GetGas indicates an expected call of GetGas.
func (mr *MockGasTxMockRecorder) GetGas() *gomock.Call {
	mr.mock.ctrl.T.Helper()
	return mr.mock.ctrl.RecordCallWithMethodType(mr.mock, "GetGas", reflect.TypeOf((*MockGasTx)(nil).GetGas))
}

// MockProposalTxVerifier is a mock of ProposalTxVerifier interface.
type MockProposalTxVerifier struct {
	ctrl     *gomock.Controller
	recorder *MockProposalTxVerifierMockRecorder
}

// MockProposalTxVerifierMockRecorder is the mock recorder for MockProposalTxVerifier.
type MockProposalTxVerifierMockRecorder struct {
	mock *MockProposalTxVerifier
}

// NewMockProposalTxVerifier creates a new mock instance.
func NewMockProposalTxVerifier(ctrl *gomock.Controller) *MockProposalTxVerifier {
	mock := &MockProposalTxVerifier{ctrl: ctrl}
	mock.recorder = &MockProposalTxVerifierMockRecorder{mock}
	return mock
}

// EXPECT returns an object that allows the caller to indicate expected use.
func (m *MockProposalTxVerifier) EXPECT() *MockProposalTxVerifierMockRecorder {
	return m.recorder
}

// PrepareProposalVerifyTx mocks base method.
func (m *MockProposalTxVerifier) PrepareProposalVerifyTx(tx types.Tx) ([]byte, error) {
	m.ctrl.T.Helper()
	ret := m.ctrl.Call(m, "PrepareProposalVerifyTx", tx)
	ret0, _ := ret[0].([]byte)
	ret1, _ := ret[1].(error)
	return ret0, ret1
}

// PrepareProposalVerifyTx indicates an expected call of PrepareProposalVerifyTx.
func (mr *MockProposalTxVerifierMockRecorder) PrepareProposalVerifyTx(tx interface{}) *gomock.Call {
	mr.mock.ctrl.T.Helper()
	return mr.mock.ctrl.RecordCallWithMethodType(mr.mock, "PrepareProposalVerifyTx", reflect.TypeOf((*MockProposalTxVerifier)(nil).PrepareProposalVerifyTx), tx)
}

// ProcessProposalVerifyTx mocks base method.
func (m *MockProposalTxVerifier) ProcessProposalVerifyTx(txBz []byte) (types.Tx, uint64, error) {
	m.ctrl.T.Helper()
	ret := m.ctrl.Call(m, "ProcessProposalVerifyTx", txBz)
	ret0, _ := ret[0].(types.Tx)
	ret1, _ := ret[1].(uint64)
	ret2, _ := ret[2].(error)
	return ret0, ret1, ret2
}

// ProcessProposalVerifyTx indicates an expected call of ProcessProposalVerifyTx.
func (mr *MockProposalTxVerifierMockRecorder) ProcessProposalVerifyTx(txBz interface{}) *gomock.Call {
	mr.mock.ctrl.T.Helper()
	return mr.mock.ctrl.RecordCallWithMethodType(mr.mock, "ProcessProposalVerifyTx", reflect.TypeOf((*MockProposalTxVerifier)(nil).ProcessProposalVerifyTx), txBz)
}

// TxDecode mocks base method.
func (m *MockProposalTxVerifier) TxDecode(txBz []byte) (types.Tx, error) {
	m.ctrl.T.Helper()
	ret := m.ctrl.Call(m, "TxDecode", txBz)
	ret0, _ := ret[0].(types.Tx)
	ret1, _ := ret[1].(error)
	return ret0, ret1
}

// TxDecode indicates an expected call of TxDecode.
func (mr *MockProposalTxVerifierMockRecorder) TxDecode(txBz interface{}) *gomock.Call {
	mr.mock.ctrl.T.Helper()
	return mr.mock.ctrl.RecordCallWithMethodType(mr.mock, "TxDecode", reflect.TypeOf((*MockProposalTxVerifier)(nil).TxDecode), txBz)
}

// TxEncode mocks base method.
func (m *MockProposalTxVerifier) TxEncode(tx types.Tx) ([]byte, error) {
	m.ctrl.T.Helper()
	ret := m.ctrl.Call(m, "TxEncode", tx)
	ret0, _ := ret[0].([]byte)
	ret1, _ := ret[1].(error)
	return ret0, ret1
}

// TxEncode indicates an expected call of TxEncode.
func (mr *MockProposalTxVerifierMockRecorder) TxEncode(tx interface{}) *gomock.Call {
	mr.mock.ctrl.T.Helper()
	return mr.mock.ctrl.RecordCallWithMethodType(mr.mock, "TxEncode", reflect.TypeOf((*MockProposalTxVerifier)(nil).TxEncode), tx)
}

// MockTxSelector is a mock of TxSelector interface.
type MockTxSelector struct {
	ctrl     *gomock.Controller
	recorder *MockTxSelectorMockRecorder
}

// MockTxSelectorMockRecorder is the mock recorder for MockTxSelector.
type MockTxSelectorMockRecorder struct {
	mock *MockTxSelector
}

// NewMockTxSelector creates a new mock instance.
func NewMockTxSelector(ctrl *gomock.Controller) *MockTxSelector {
	mock := &MockTxSelector{ctrl: ctrl}
	mock.recorder = &MockTxSelectorMockRecorder{mock}
	return mock
}

// EXPECT returns an object that allows the caller to indicate expected use.
func (m *MockTxSelector) EXPECT() *MockTxSelectorMockRecorder {
	return m.recorder
}

// Clear mocks base method.
func (m *MockTxSelector) Clear() {
	m.ctrl.T.Helper()
	m.ctrl.Call(m, "Clear")
}

// Clear indicates an expected call of Clear.
func (mr *MockTxSelectorMockRecorder) Clear() *gomock.Call {
	mr.mock.ctrl.T.Helper()
	return mr.mock.ctrl.RecordCallWithMethodType(mr.mock, "Clear", reflect.TypeOf((*MockTxSelector)(nil).Clear))
}

// SelectTxForProposal mocks base method.
func (m *MockTxSelector) SelectTxForProposal(ctx context.Context, maxTxBytes, maxBlockGas uint64, memTx types.Tx, txBz []byte, gasWanted uint64) bool {
	m.ctrl.T.Helper()
	ret := m.ctrl.Call(m, "SelectTxForProposal", ctx, maxTxBytes, maxBlockGas, memTx, txBz, gasWanted)
	ret0, _ := ret[0].(bool)
	return ret0
}

// SelectTxForProposal indicates an expected call of SelectTxForProposal.
func (mr *MockTxSelectorMockRecorder) SelectTxForProposal(ctx, maxTxBytes, maxBlockGas, memTx, txBz, gasWanted interface{}) *gomock.Call {
	mr.mock.ctrl.T.Helper()
	return mr.mock.ctrl.RecordCallWithMethodType(mr.mock, "SelectTxForProposal", reflect.TypeOf((*MockTxSelector)(nil).SelectTxForProposal), ctx, maxTxBytes, maxBlockGas, memTx, txBz, gasWanted)
}

// SelectedTxs mocks base method.
func (m *MockTxSelector) SelectedTxs(ctx context.Context) [][]byte {
	m.ctrl.T.Helper()
	ret := m.ctrl.Call(m, "SelectedTxs", ctx)
	ret0, _ := ret[0].([][]byte)
	return ret0
}

// SelectedTxs indicates an expected call of SelectedTxs.
func (mr *MockTxSelectorMockRecorder) SelectedTxs(ctx interface{}) *gomock.Call {
	mr.mock.ctrl.T.Helper()
	return mr.mock.ctrl.RecordCallWithMethodType(mr.mock, "SelectedTxs", reflect.TypeOf((*MockTxSelector)(nil).SelectedTxs), ctx)
}
