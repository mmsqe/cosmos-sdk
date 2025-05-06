package types_test

import (
	"bytes"
	"encoding/json"
	"fmt"
	"math/big"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"github.com/stretchr/testify/suite"
	"sigs.k8s.io/yaml"

	sdk "github.com/cosmos/cosmos-sdk/types"
)

type decimalTestSuite struct {
	suite.Suite
}

func TestDecimalTestSuite(t *testing.T) {
	suite.Run(t, new(decimalTestSuite))
}

func TestDecApproxEq(t *testing.T) {
	// d1 = 0.55, d2 = 0.6, tol = 0.1
	d1 := sdk.NewDecWithPrec(55, 2)
	d2 := sdk.NewDecWithPrec(6, 1)
	tol := sdk.NewDecWithPrec(1, 1)

	require.True(sdk.DecApproxEq(t, d1, d2, tol))

	// d1 = 0.55, d2 = 0.6, tol = 1E-5
	d1 = sdk.NewDecWithPrec(55, 2)
	d2 = sdk.NewDecWithPrec(6, 1)
	tol = sdk.NewDecWithPrec(1, 5)

	require.False(sdk.DecApproxEq(t, d1, d2, tol))

	// d1 = 0.6, d2 = 0.61, tol = 0.01
	d1 = sdk.NewDecWithPrec(6, 1)
	d2 = sdk.NewDecWithPrec(61, 2)
	tol = sdk.NewDecWithPrec(1, 2)

	require.True(sdk.DecApproxEq(t, d1, d2, tol))
}

// create a decimal from a decimal string (ex. "1234.5678")
func (s *decimalTestSuite) mustNewDecFromStr(str string) (d sdk.Dec) {
	d, err := sdk.NewDecFromStr(str)
	s.Require().NoError(err)

	return d
}

func (s *decimalTestSuite) TestNewDecFromStr() {
	largeBigInt, ok := new(big.Int).SetString("3144605511029693144278234343371835", 10)
	s.Require().True(ok)

	largerBigInt, ok := new(big.Int).SetString("8888888888888888888888888888888888888888888888888888888888888888888844444440", 10)
	s.Require().True(ok)

	largestBigInt, ok := new(big.Int).SetString("33499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433535", 10)
	s.Require().True(ok)

	tests := []struct {
		decimalStr string
		expErr     bool
		exp        sdk.Dec
	}{
		{"", true, sdk.Dec{}},
		{"0.-75", true, sdk.Dec{}},
		{"0", false, sdk.NewDec(0)},
		{"1", false, sdk.NewDec(1)},
		{"1.1", false, sdk.NewDecWithPrec(11, 1)},
		{"0.75", false, sdk.NewDecWithPrec(75, 2)},
		{"0.8", false, sdk.NewDecWithPrec(8, 1)},
		{"0.11111", false, sdk.NewDecWithPrec(11111, 5)},
		{"314460551102969.3144278234343371835", true, sdk.NewDec(3141203149163817869)},
		{
			"314460551102969314427823434337.1835718092488231350",
			true, sdk.NewDecFromBigIntWithPrec(largeBigInt, 4),
		},
		{
			"314460551102969314427823434337.1835",
			false, sdk.NewDecFromBigIntWithPrec(largeBigInt, 4),
		},
		{".", true, sdk.Dec{}},
		{".0", true, sdk.NewDec(0)},
		{"1.", true, sdk.NewDec(1)},
		{"foobar", true, sdk.Dec{}},
		{"0.foobar", true, sdk.Dec{}},
		{"0.foobar.", true, sdk.Dec{}},
		{"8888888888888888888888888888888888888888888888888888888888888888888844444440", false, sdk.NewDecFromBigInt(largerBigInt)},
		{"33499189745056880149688856635597007162669032647290798121690100488888732861290.034376435130433535", false, sdk.NewDecFromBigIntWithPrec(largestBigInt, 18)},
		{"133499189745056880149688856635597007162669032647290798121690100488888732861291", true, sdk.Dec{}},
		{"115792089237316195423570985008687907853269984665640564039457584007913129639936", true, sdk.Dec{}}, // 2^256
	}

	for tcIndex, tc := range tests {
		res, err := sdk.NewDecFromStr(tc.decimalStr)
		if tc.expErr {
			s.Require().NotNil(err, "error expected, decimalStr %v, tc %v", tc.decimalStr, tcIndex)
		} else {
			s.Require().Nil(err, "unexpected error, decimalStr %v, tc %v", tc.decimalStr, tcIndex)
			s.Require().True(res.Equal(tc.exp), "equality was incorrect, res %v, expTruncated %v, tc %v", res, tc.exp, tcIndex)
		}

		// negative tc
		res, err = sdk.NewDecFromStr("-" + tc.decimalStr)
		if tc.expErr {
			s.Require().NotNil(err, "error expected, decimalStr %v, tc %v", tc.decimalStr, tcIndex)
		} else {
			s.Require().Nil(err, "unexpected error, decimalStr %v, tc %v", tc.decimalStr, tcIndex)
			exp := tc.exp.Mul(sdk.NewDec(-1))
			s.Require().True(res.Equal(exp), "equality was incorrect, res %v, expTruncated %v, tc %v", res, exp, tcIndex)
		}
	}
}

func (s *decimalTestSuite) TestDecString() {
	tests := []struct {
		d    sdk.Dec
		want string
	}{
		{sdk.NewDec(0), "0.000000000000000000"},
		{sdk.NewDec(1), "1.000000000000000000"},
		{sdk.NewDec(10), "10.000000000000000000"},
		{sdk.NewDec(12340), "12340.000000000000000000"},
		{sdk.NewDecWithPrec(12340, 4), "1.234000000000000000"},
		{sdk.NewDecWithPrec(12340, 5), "0.123400000000000000"},
		{sdk.NewDecWithPrec(12340, 8), "0.000123400000000000"},
		{sdk.NewDecWithPrec(1009009009009009009, 17), "10.090090090090090090"},
	}
	for tcIndex, tc := range tests {
		s.Require().Equal(tc.want, tc.d.String(), "bad String(), index: %v", tcIndex)
	}
}

func (s *decimalTestSuite) TestDecFloat64() {
	tests := []struct {
		d    sdk.Dec
		want float64
	}{
		{sdk.NewDec(0), 0.000000000000000000},
		{sdk.NewDec(1), 1.000000000000000000},
		{sdk.NewDec(10), 10.000000000000000000},
		{sdk.NewDec(12340), 12340.000000000000000000},
		{sdk.NewDecWithPrec(12340, 4), 1.234000000000000000},
		{sdk.NewDecWithPrec(12340, 5), 0.123400000000000000},
		{sdk.NewDecWithPrec(12340, 8), 0.000123400000000000},
		{sdk.NewDecWithPrec(1009009009009009009, 17), 10.090090090090090090},
	}
	for tcIndex, tc := range tests {
		value, err := tc.d.Float64()
		s.Require().Nil(err, "error getting Float64(), index: %v", tcIndex)
		s.Require().Equal(tc.want, value, "bad Float64(), index: %v", tcIndex)
		s.Require().Equal(tc.want, tc.d.MustFloat64(), "bad MustFloat64(), index: %v", tcIndex)
	}
}

func (s *decimalTestSuite) TestEqualities() {
	tests := []struct {
		d1, d2     sdk.Dec
		gt, lt, eq bool
	}{
		{sdk.NewDec(0), sdk.NewDec(0), false, false, true},
		{sdk.NewDecWithPrec(0, 2), sdk.NewDecWithPrec(0, 4), false, false, true},
		{sdk.NewDecWithPrec(100, 0), sdk.NewDecWithPrec(100, 0), false, false, true},
		{sdk.NewDecWithPrec(-100, 0), sdk.NewDecWithPrec(-100, 0), false, false, true},
		{sdk.NewDecWithPrec(-1, 1), sdk.NewDecWithPrec(-1, 1), false, false, true},
		{sdk.NewDecWithPrec(3333, 3), sdk.NewDecWithPrec(3333, 3), false, false, true},

		{sdk.NewDecWithPrec(0, 0), sdk.NewDecWithPrec(3333, 3), false, true, false},
		{sdk.NewDecWithPrec(0, 0), sdk.NewDecWithPrec(100, 0), false, true, false},
		{sdk.NewDecWithPrec(-1, 0), sdk.NewDecWithPrec(3333, 3), false, true, false},
		{sdk.NewDecWithPrec(-1, 0), sdk.NewDecWithPrec(100, 0), false, true, false},
		{sdk.NewDecWithPrec(1111, 3), sdk.NewDecWithPrec(100, 0), false, true, false},
		{sdk.NewDecWithPrec(1111, 3), sdk.NewDecWithPrec(3333, 3), false, true, false},
		{sdk.NewDecWithPrec(-3333, 3), sdk.NewDecWithPrec(-1111, 3), false, true, false},

		{sdk.NewDecWithPrec(3333, 3), sdk.NewDecWithPrec(0, 0), true, false, false},
		{sdk.NewDecWithPrec(100, 0), sdk.NewDecWithPrec(0, 0), true, false, false},
		{sdk.NewDecWithPrec(3333, 3), sdk.NewDecWithPrec(-1, 0), true, false, false},
		{sdk.NewDecWithPrec(100, 0), sdk.NewDecWithPrec(-1, 0), true, false, false},
		{sdk.NewDecWithPrec(100, 0), sdk.NewDecWithPrec(1111, 3), true, false, false},
		{sdk.NewDecWithPrec(3333, 3), sdk.NewDecWithPrec(1111, 3), true, false, false},
		{sdk.NewDecWithPrec(-1111, 3), sdk.NewDecWithPrec(-3333, 3), true, false, false},
	}

	for tcIndex, tc := range tests {
		s.Require().Equal(tc.gt, tc.d1.GT(tc.d2), "GT result is incorrect, tc %d", tcIndex)
		s.Require().Equal(tc.lt, tc.d1.LT(tc.d2), "LT result is incorrect, tc %d", tcIndex)
		s.Require().Equal(tc.eq, tc.d1.Equal(tc.d2), "equality result is incorrect, tc %d", tcIndex)
	}
}

func (s *decimalTestSuite) TestDecsEqual() {
	tests := []struct {
		d1s, d2s []sdk.Dec
		eq       bool
	}{
		{[]sdk.Dec{sdk.NewDec(0)}, []sdk.Dec{sdk.NewDec(0)}, true},
		{[]sdk.Dec{sdk.NewDec(0)}, []sdk.Dec{sdk.NewDec(1)}, false},
		{[]sdk.Dec{sdk.NewDec(0)}, []sdk.Dec{}, false},
		{[]sdk.Dec{sdk.NewDec(0), sdk.NewDec(1)}, []sdk.Dec{sdk.NewDec(0), sdk.NewDec(1)}, true},
		{[]sdk.Dec{sdk.NewDec(1), sdk.NewDec(0)}, []sdk.Dec{sdk.NewDec(1), sdk.NewDec(0)}, true},
		{[]sdk.Dec{sdk.NewDec(1), sdk.NewDec(0)}, []sdk.Dec{sdk.NewDec(0), sdk.NewDec(1)}, false},
		{[]sdk.Dec{sdk.NewDec(1), sdk.NewDec(0)}, []sdk.Dec{sdk.NewDec(1)}, false},
		{[]sdk.Dec{sdk.NewDec(1), sdk.NewDec(2)}, []sdk.Dec{sdk.NewDec(2), sdk.NewDec(4)}, false},
		{[]sdk.Dec{sdk.NewDec(3), sdk.NewDec(18)}, []sdk.Dec{sdk.NewDec(1), sdk.NewDec(6)}, false},
	}

	for tcIndex, tc := range tests {
		s.Require().Equal(tc.eq, sdk.DecsEqual(tc.d1s, tc.d2s), "equality of decional arrays is incorrect, tc %d", tcIndex)
		s.Require().Equal(tc.eq, sdk.DecsEqual(tc.d2s, tc.d1s), "equality of decional arrays is incorrect (converse), tc %d", tcIndex)
	}
}

func (s *decimalTestSuite) TestArithmetic() {
	tests := []struct {
		d1, d2                                sdk.Dec
		expMul, expMulTruncate, expMulRoundUp sdk.Dec
		expQuo, expQuoRoundUp, expQuoTruncate sdk.Dec
		expAdd, expSub                        sdk.Dec
	}{
		//  d1         d2         MUL    MulTruncate   MulRoundUp    QUO    QUORoundUp QUOTrunctate  ADD         SUB
		{sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0)},
		{sdk.NewDec(1), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(1), sdk.NewDec(1)},
		{sdk.NewDec(0), sdk.NewDec(1), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(1), sdk.NewDec(-1)},
		{sdk.NewDec(0), sdk.NewDec(-1), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(-1), sdk.NewDec(1)},
		{sdk.NewDec(-1), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(0), sdk.NewDec(-1), sdk.NewDec(-1)},

		{sdk.NewDec(1), sdk.NewDec(1), sdk.NewDec(1), sdk.NewDec(1), sdk.NewDec(1), sdk.NewDec(1), sdk.NewDec(1), sdk.NewDec(1), sdk.NewDec(2), sdk.NewDec(0)},
		{sdk.NewDec(-1), sdk.NewDec(-1), sdk.NewDec(1), sdk.NewDec(1), sdk.NewDec(1), sdk.NewDec(1), sdk.NewDec(1), sdk.NewDec(1), sdk.NewDec(-2), sdk.NewDec(0)},
		{sdk.NewDec(1), sdk.NewDec(-1), sdk.NewDec(-1), sdk.NewDec(-1), sdk.NewDec(-1), sdk.NewDec(-1), sdk.NewDec(-1), sdk.NewDec(-1), sdk.NewDec(0), sdk.NewDec(2)},
		{sdk.NewDec(-1), sdk.NewDec(1), sdk.NewDec(-1), sdk.NewDec(-1), sdk.NewDec(-1), sdk.NewDec(-1), sdk.NewDec(-1), sdk.NewDec(-1), sdk.NewDec(0), sdk.NewDec(-2)},

		{
			sdk.NewDec(3), sdk.NewDec(7), sdk.NewDec(21), sdk.NewDec(21), sdk.NewDec(21),
			sdk.NewDecWithPrec(428571428571428571, 18), sdk.NewDecWithPrec(428571428571428572, 18), sdk.NewDecWithPrec(428571428571428571, 18),
			sdk.NewDec(10), sdk.NewDec(-4),
		},
		{
			sdk.NewDec(2), sdk.NewDec(4), sdk.NewDec(8), sdk.NewDec(8), sdk.NewDec(8), sdk.NewDecWithPrec(5, 1), sdk.NewDecWithPrec(5, 1), sdk.NewDecWithPrec(5, 1),
			sdk.NewDec(6), sdk.NewDec(-2),
		},

		{sdk.NewDec(100), sdk.NewDec(100), sdk.NewDec(10000), sdk.NewDec(10000), sdk.NewDec(10000), sdk.NewDec(1), sdk.NewDec(1), sdk.NewDec(1), sdk.NewDec(200), sdk.NewDec(0)},

		{
			sdk.NewDecWithPrec(15, 1), sdk.NewDecWithPrec(15, 1), sdk.NewDecWithPrec(225, 2), sdk.NewDecWithPrec(225, 2), sdk.NewDecWithPrec(225, 2),
			sdk.NewDec(1), sdk.NewDec(1), sdk.NewDec(1), sdk.NewDec(3), sdk.NewDec(0),
		},
		{
			sdk.NewDecWithPrec(3333, 4), sdk.NewDecWithPrec(333, 4), sdk.NewDecWithPrec(1109889, 8), sdk.NewDecWithPrec(1109889, 8), sdk.NewDecWithPrec(1109889, 8),
			sdk.MustNewDecFromStr("10.009009009009009009"), sdk.MustNewDecFromStr("10.009009009009009010"), sdk.MustNewDecFromStr("10.009009009009009009"),
			sdk.NewDecWithPrec(3666, 4), sdk.NewDecWithPrec(3, 1),
		},
	}

	for tcIndex, tc := range tests {

		resAdd := tc.d1.Add(tc.d2)
		resSub := tc.d1.Sub(tc.d2)
		resMul := tc.d1.Mul(tc.d2)
		resMulTruncate := tc.d1.MulTruncate(tc.d2)
		s.Require().True(tc.expAdd.Equal(resAdd), "expTruncated %v, res %v, tc %d", tc.expAdd, resAdd, tcIndex)
		s.Require().True(tc.expSub.Equal(resSub), "expTruncated %v, res %v, tc %d", tc.expSub, resSub, tcIndex)
		s.Require().True(tc.expMul.Equal(resMul), "expTruncated %v, res %v, tc %d", tc.expMul, resMul, tcIndex)
		s.Require().True(tc.expMulTruncate.Equal(resMulTruncate), "expTruncated %v, res %v, tc %d", tc.expMulTruncate, resMulTruncate, tcIndex)

		if tc.d2.IsZero() { // panic for divide by zero
			s.Require().Panics(func() { tc.d1.Quo(tc.d2) })
		} else {
			resQuo := tc.d1.Quo(tc.d2)
			s.Require().True(tc.expQuo.Equal(resQuo), "expTruncated %v, res %v, tc %d", tc.expQuo.String(), resQuo.String(), tcIndex)

			resQuoRoundUp := tc.d1.QuoRoundUp(tc.d2)
			s.Require().True(tc.expQuoRoundUp.Equal(resQuoRoundUp), "expTruncated %v, res %v, tc %d",
				tc.expQuoRoundUp.String(), resQuoRoundUp.String(), tcIndex)

			resQuoTruncate := tc.d1.QuoTruncate(tc.d2)
			s.Require().True(tc.expQuoTruncate.Equal(resQuoTruncate), "expTruncated %v, res %v, tc %d",
				tc.expQuoTruncate.String(), resQuoTruncate.String(), tcIndex)
		}
	}
}

func (s *decimalTestSuite) TestBankerRoundChop() {
	tests := []struct {
		d1  sdk.Dec
		exp int64
	}{
		{s.mustNewDecFromStr("0.25"), 0},
		{s.mustNewDecFromStr("0"), 0},
		{s.mustNewDecFromStr("1"), 1},
		{s.mustNewDecFromStr("0.75"), 1},
		{s.mustNewDecFromStr("0.5"), 0},
		{s.mustNewDecFromStr("7.5"), 8},
		{s.mustNewDecFromStr("1.5"), 2},
		{s.mustNewDecFromStr("2.5"), 2},
		{s.mustNewDecFromStr("0.545"), 1}, // 0.545-> 1 even though 5 is first decimal and 1 not even
		{s.mustNewDecFromStr("1.545"), 2},
	}

	for tcIndex, tc := range tests {
		resNeg := tc.d1.Neg().RoundInt64()
		s.Require().Equal(-1*tc.exp, resNeg, "negative tc %d", tcIndex)

		resPos := tc.d1.RoundInt64()
		s.Require().Equal(tc.exp, resPos, "positive tc %d", tcIndex)
	}
}

func (s *decimalTestSuite) TestTruncate() {
	tests := []struct {
		d1  sdk.Dec
		exp int64
	}{
		{s.mustNewDecFromStr("0"), 0},
		{s.mustNewDecFromStr("0.25"), 0},
		{s.mustNewDecFromStr("0.75"), 0},
		{s.mustNewDecFromStr("1"), 1},
		{s.mustNewDecFromStr("1.5"), 1},
		{s.mustNewDecFromStr("7.5"), 7},
		{s.mustNewDecFromStr("7.6"), 7},
		{s.mustNewDecFromStr("7.4"), 7},
		{s.mustNewDecFromStr("100.1"), 100},
		{s.mustNewDecFromStr("1000.1"), 1000},
	}

	for tcIndex, tc := range tests {
		resNeg := tc.d1.Neg().TruncateInt64()
		s.Require().Equal(-1*tc.exp, resNeg, "negative tc %d", tcIndex)

		resPos := tc.d1.TruncateInt64()
		s.Require().Equal(tc.exp, resPos, "positive tc %d", tcIndex)
	}
}

func (s *decimalTestSuite) TestStringOverflow() {
	// two random 64 bit primes
	dec1, err := sdk.NewDecFromStr("51643150036226787134389711697696177267")
	s.Require().NoError(err)
	dec2, err := sdk.NewDecFromStr("-31798496660535729618459429845579852627")
	s.Require().NoError(err)
	dec3 := dec1.Add(dec2)
	s.Require().Equal(
		"19844653375691057515930281852116324640.000000000000000000",
		dec3.String(),
	)
}

func (s *decimalTestSuite) TestDecMulInt() {
	tests := []struct {
		sdkDec sdk.Dec
		sdkInt sdk.Int
		want   sdk.Dec
	}{
		{sdk.NewDec(10), sdk.NewInt(2), sdk.NewDec(20)},
		{sdk.NewDec(1000000), sdk.NewInt(100), sdk.NewDec(100000000)},
		{sdk.NewDecWithPrec(1, 1), sdk.NewInt(10), sdk.NewDec(1)},
		{sdk.NewDecWithPrec(1, 5), sdk.NewInt(20), sdk.NewDecWithPrec(2, 4)},
	}
	for i, tc := range tests {
		got := tc.sdkDec.MulInt(tc.sdkInt)
		s.Require().Equal(tc.want, got, "Incorrect result on test case %d", i)
	}
}

func (s *decimalTestSuite) TestDecCeil() {
	testCases := []struct {
		input    sdk.Dec
		expected sdk.Dec
	}{
		{sdk.NewDecWithPrec(1000000000000000, sdk.Precision), sdk.NewDec(1)},      // 0.001 => 1.0
		{sdk.NewDecWithPrec(-1000000000000000, sdk.Precision), sdk.ZeroDec()},     // -0.001 => 0.0
		{sdk.ZeroDec(), sdk.ZeroDec()},                                            // 0.0 => 0.0
		{sdk.NewDecWithPrec(900000000000000000, sdk.Precision), sdk.NewDec(1)},    // 0.9 => 1.0
		{sdk.NewDecWithPrec(4001000000000000000, sdk.Precision), sdk.NewDec(5)},   // 4.001 => 5.0
		{sdk.NewDecWithPrec(-4001000000000000000, sdk.Precision), sdk.NewDec(-4)}, // -4.001 => -4.0
		{sdk.NewDecWithPrec(4700000000000000000, sdk.Precision), sdk.NewDec(5)},   // 4.7 => 5.0
		{sdk.NewDecWithPrec(-4700000000000000000, sdk.Precision), sdk.NewDec(-4)}, // -4.7 => -4.0
	}

	for i, tc := range testCases {
		res := tc.input.Ceil()
		s.Require().Equal(tc.expected, res, "unexpected result for test case %d, input: %v", i, tc.input)
	}
}

func (s *decimalTestSuite) TestCeilOverflow() {
	// (2^256 * 10^18 -1) / 10^18
	d, err := sdk.NewDecFromStr("115792089237316195423570985008687907853269984665640564039457584007913129639935.999999999999999999")
	s.Require().NoError(err)
	s.Require().True(d.IsInValidRange())
	// this call panics because the value is too large
	s.Require().Panics(func() { d.Ceil() }, "Ceil should panic on overflow")
}

func (s *decimalTestSuite) TestPower() {
	testCases := []struct {
		input    sdk.Dec
		power    uint64
		expected sdk.Dec
	}{
		{sdk.NewDec(100), 0, sdk.OneDec()},                                                 // 10 ^ (0) => 1.0
		{sdk.OneDec(), 10, sdk.OneDec()},                                                   // 1.0 ^ (10) => 1.0
		{sdk.NewDecWithPrec(5, 1), 2, sdk.NewDecWithPrec(25, 2)},                           // 0.5 ^ 2 => 0.25
		{sdk.NewDecWithPrec(2, 1), 2, sdk.NewDecWithPrec(4, 2)},                            // 0.2 ^ 2 => 0.04
		{sdk.NewDecFromInt(sdk.NewInt(3)), 3, sdk.NewDecFromInt(sdk.NewInt(27))},           // 3 ^ 3 => 27
		{sdk.NewDecFromInt(sdk.NewInt(-3)), 4, sdk.NewDecFromInt(sdk.NewInt(81))},          // -3 ^ 4 = 81
		{sdk.NewDecWithPrec(1414213562373095049, 18), 2, sdk.NewDecFromInt(sdk.NewInt(2))}, // 1.414213562373095049 ^ 2 = 2
	}

	for i, tc := range testCases {
		res := tc.input.Power(tc.power)
		s.Require().True(tc.expected.Sub(res).Abs().LTE(sdk.SmallestDec()), "unexpected result for test case %d, normal power, input: %v", i, tc.input)

		mutableInput := tc.input
		mutableInput.PowerMut(tc.power)
		s.Require().True(tc.expected.Sub(mutableInput).Abs().LTE(sdk.SmallestDec()),
			"unexpected result for test case %d, input %v", i, tc.input)
		s.Require().True(res.Equal(tc.input), "unexpected result for test case %d, mutable power, input: %v", i, tc.input)
	}
}

func (s *decimalTestSuite) TestApproxRoot() {
	testCases := []struct {
		input    sdk.Dec
		root     uint64
		expected sdk.Dec
	}{
		{sdk.NewDecFromInt(sdk.NewInt(2)), 0, sdk.OneDec()},                                    // 2 ^ 0 => 1.0
		{sdk.NewDecWithPrec(4, 2), 0, sdk.OneDec()},                                            // 0.04 ^ 0 => 1.0
		{sdk.NewDec(0), 1, sdk.NewDec(0)},                                                      // 0 ^ 1 => 0
		{sdk.OneDec(), 10, sdk.OneDec()},                                                       // 1.0 ^ (0.1) => 1.0
		{sdk.NewDecWithPrec(25, 2), 2, sdk.NewDecWithPrec(5, 1)},                               // 0.25 ^ (0.5) => 0.5
		{sdk.NewDecWithPrec(4, 2), 2, sdk.NewDecWithPrec(2, 1)},                                // 0.04 ^ (0.5) => 0.2
		{sdk.NewDecFromInt(sdk.NewInt(27)), 3, sdk.NewDecFromInt(sdk.NewInt(3))},               // 27 ^ (1/3) => 3
		{sdk.NewDecFromInt(sdk.NewInt(-81)), 4, sdk.NewDecFromInt(sdk.NewInt(-3))},             // -81 ^ (0.25) => -3
		{sdk.NewDecFromInt(sdk.NewInt(2)), 2, sdk.NewDecWithPrec(1414213562373095049, 18)},     // 2 ^ (0.5) => 1.414213562373095049
		{sdk.NewDecWithPrec(1005, 3), 31536000, sdk.MustNewDecFromStr("1.000000000158153904")}, // 1.005 ^ (1/31536000) ≈ 1.00000000016
		{sdk.SmallestDec(), 2, sdk.NewDecWithPrec(1, 9)},                                       // 1e-18 ^ (0.5) => 1e-9
		{sdk.SmallestDec(), 3, sdk.MustNewDecFromStr("0.000000999999999997")},                  // 1e-18 ^ (1/3) => 1e-6
		{sdk.NewDecWithPrec(1, 8), 3, sdk.MustNewDecFromStr("0.002154434690031900")},           // 1e-8 ^ (1/3) ≈ 0.00215443469
		{sdk.MustNewDecFromStr("9000002314687921634000000000000000000021394871242000000000000000"), 2, sdk.MustNewDecFromStr("94868342004527103646332858502867.899477053226766107")},
	}

	// In the case of 1e-8 ^ (1/3), the result repeats every 5 iterations starting from iteration 24
	// (i.e. 24, 29, 34, ... give the same result) and never converges enough. The maximum number of
	// iterations (300) causes the result at iteration 300 to be returned, regardless of convergence.

	for i, tc := range testCases {
		res, err := tc.input.ApproxRoot(tc.root)
		s.Require().NoError(err)
		s.Require().True(tc.expected.Sub(res).Abs().LTE(sdk.SmallestDec()), "unexpected result for test case %d, input: %v", i, tc.input)
	}
}

func (s *decimalTestSuite) TestApproxSqrt() {
	testCases := []struct {
		input    sdk.Dec
		expected sdk.Dec
	}{
		{sdk.OneDec(), sdk.OneDec()},                                 // 1.0 => 1.0
		{sdk.NewDecWithPrec(25, 2), sdk.NewDecWithPrec(5, 1)},        // 0.25 => 0.5
		{sdk.NewDecWithPrec(4, 2), sdk.NewDecWithPrec(2, 1)},         // 0.09 => 0.3
		{sdk.NewDec(9), sdk.NewDecFromInt(sdk.NewInt(3))},            // 9 => 3
		{sdk.NewDec(-9), sdk.NewDecFromInt(sdk.NewInt(-3))},          // -9 => -3
		{sdk.NewDec(2), sdk.NewDecWithPrec(1414213562373095049, 18)}, // 2 => 1.414213562373095049
		{ // 2^127 - 1 => 13043817825332782212.3495718062525083688 which rounds to 13043817825332782212.3495718062525083689
			sdk.NewDec(2).Power(127).Sub(sdk.OneDec()),
			sdk.MustNewDecFromStr("13043817825332782212.349571806252508369"),
		},
		{sdk.MustNewDecFromStr("1.000000011823380862"), sdk.MustNewDecFromStr("1.000000005911690414")},
	}

	for i, tc := range testCases {
		res, err := tc.input.ApproxSqrt()
		s.Require().NoError(err)
		s.Require().Equal(tc.expected, res, "unexpected result for test case %d, input: %v", i, tc.input)
	}
}

func (s *decimalTestSuite) TestDecSortableBytes() {
	tests := []struct {
		d    sdk.Dec
		want []byte
	}{
		{sdk.NewDec(0), []byte("000000000000000000.000000000000000000")},
		{sdk.NewDec(1), []byte("000000000000000001.000000000000000000")},
		{sdk.NewDec(10), []byte("000000000000000010.000000000000000000")},
		{sdk.NewDec(12340), []byte("000000000000012340.000000000000000000")},
		{sdk.NewDecWithPrec(12340, 4), []byte("000000000000000001.234000000000000000")},
		{sdk.NewDecWithPrec(12340, 5), []byte("000000000000000000.123400000000000000")},
		{sdk.NewDecWithPrec(12340, 8), []byte("000000000000000000.000123400000000000")},
		{sdk.NewDecWithPrec(1009009009009009009, 17), []byte("000000000000000010.090090090090090090")},
		{sdk.NewDecWithPrec(-1009009009009009009, 17), []byte("-000000000000000010.090090090090090090")},
		{sdk.NewDec(1000000000000000000), []byte("max")},
		{sdk.NewDec(-1000000000000000000), []byte("--")},
	}
	for tcIndex, tc := range tests {
		s.Require().Equal(tc.want, sdk.SortableDecBytes(tc.d), "bad String(), index: %v", tcIndex)
	}

	s.Require().Panics(func() { sdk.SortableDecBytes(sdk.NewDec(1000000000000000001)) })
	s.Require().Panics(func() { sdk.SortableDecBytes(sdk.NewDec(-1000000000000000001)) })
}

func (s *decimalTestSuite) TestDecEncoding() {
	largestBigInt, ok := new(big.Int).SetString("33499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433535", 10)
	s.Require().True(ok)

	smallestBigInt, ok := new(big.Int).SetString("-33499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433535", 10)
	s.Require().True(ok)

	const maxDecBitLen = 315
	maxInt, ok := new(big.Int).SetString(strings.Repeat("1", maxDecBitLen), 2)
	s.Require().True(ok)

	testCases := []struct {
		input   sdk.Dec
		rawBz   string
		jsonStr string
		yamlStr string
	}{
		{
			sdk.NewDec(0), "30",
			"\"0.000000000000000000\"",
			"\"0.000000000000000000\"\n",
		},
		{
			sdk.NewDecWithPrec(4, 2),
			"3430303030303030303030303030303030",
			"\"0.040000000000000000\"",
			"\"0.040000000000000000\"\n",
		},
		{
			sdk.NewDecWithPrec(-4, 2),
			"2D3430303030303030303030303030303030",
			"\"-0.040000000000000000\"",
			"\"-0.040000000000000000\"\n",
		},
		{
			sdk.NewDecWithPrec(1414213562373095049, 18),
			"31343134323133353632333733303935303439",
			"\"1.414213562373095049\"",
			"\"1.414213562373095049\"\n",
		},
		{
			sdk.NewDecWithPrec(-1414213562373095049, 18),
			"2D31343134323133353632333733303935303439",
			"\"-1.414213562373095049\"",
			"\"-1.414213562373095049\"\n",
		},
		{
			sdk.NewDecFromBigIntWithPrec(largestBigInt, 18),
			"3333343939313839373435303536383830313439363838383536363335353937303037313632363639303332363437323930373938313231363930313030343838383838373332383631323930303334333736343335313330343333353335",
			"\"33499189745056880149688856635597007162669032647290798121690100488888732861290.034376435130433535\"",
			"\"33499189745056880149688856635597007162669032647290798121690100488888732861290.034376435130433535\"\n",
		},
		{
			sdk.NewDecFromBigIntWithPrec(smallestBigInt, 18),
			"2D3333343939313839373435303536383830313439363838383536363335353937303037313632363639303332363437323930373938313231363930313030343838383838373332383631323930303334333736343335313330343333353335",
			"\"-33499189745056880149688856635597007162669032647290798121690100488888732861290.034376435130433535\"",
			"\"-33499189745056880149688856635597007162669032647290798121690100488888732861290.034376435130433535\"\n",
		},
		{
			sdk.NewDecFromBigIntWithPrec(maxInt, 18),
			"3636373439353934383732353238343430303734383434343238333137373938353033353831333334353136333233363435333939303630383435303530323434343434333636343330363435303137313838323137353635323136373637",
			"\"66749594872528440074844428317798503581334516323645399060845050244444366430645.017188217565216767\"",
			"\"66749594872528440074844428317798503581334516323645399060845050244444366430645.017188217565216767\"\n",
		},
	}

	for _, tc := range testCases {
		bz, err := tc.input.Marshal()
		s.Require().NoError(err)
		s.Require().Equal(tc.rawBz, fmt.Sprintf("%X", bz))

		var other sdk.Dec
		s.Require().NoError((&other).Unmarshal(bz))
		s.Require().True(tc.input.Equal(other))

		bz, err = json.Marshal(tc.input)
		s.Require().NoError(err)
		s.Require().Equal(tc.jsonStr, string(bz))
		s.Require().NoError(json.Unmarshal(bz, &other))
		s.Require().True(tc.input.Equal(other))

		bz, err = yaml.Marshal(tc.input)
		s.Require().NoError(err)
		s.Require().Equal(tc.yamlStr, string(bz))
	}
}

// Showcase that different orders of operations causes different results.
func (s *decimalTestSuite) TestOperationOrders() {
	n1 := sdk.NewDec(10)
	n2 := sdk.NewDec(1000000010)
	s.Require().Equal(n1.Mul(n2).Quo(n2), sdk.NewDec(10))
	s.Require().NotEqual(n1.Mul(n2).Quo(n2), n1.Quo(n2).Mul(n2))
}

func BenchmarkMarshalTo(b *testing.B) {
	b.ReportAllocs()
	bis := []struct {
		in   sdk.Dec
		want []byte
	}{
		{
			sdk.NewDec(1e8), []byte{
				0x31, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30,
				0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30,
				0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30,
			},
		},
		{sdk.NewDec(0), []byte{0x30}},
	}
	data := make([]byte, 100)

	b.ReportAllocs()
	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		for _, bi := range bis {
			if n, err := bi.in.MarshalTo(data); err != nil {
				b.Fatal(err)
			} else if !bytes.Equal(data[:n], bi.want) {
				b.Fatalf("Mismatch\nGot:  % x\nWant: % x\n", data[:n], bi.want)
			}
		}
	}
}

var sink interface{}

func BenchmarkQuoMut(b *testing.B) {
	b1 := sdk.NewDec(17e2 + 8371)
	b2 := sdk.NewDec(4371)
	b.ReportAllocs()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		sink = b1.QuoMut(b2)
	}

	if sink == nil {
		b.Fatal("Benchmark did not run")
	}
	sink = (interface{})(nil)
}

func BenchmarkQuoTruncateMut(b *testing.B) {
	b1 := sdk.NewDec(17e2 + 8371)
	baseArr := make([]sdk.Dec, b.N)
	for i := 0; i < b.N; i++ {
		baseArr[i] = b1.Clone()
	}
	b2 := sdk.NewDec(4371)
	b.ReportAllocs()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		sink = baseArr[i].QuoTruncateMut(b2)
	}

	if sink == nil {
		b.Fatal("Benchmark did not run")
	}
	sink = (interface{})(nil)
}

func BenchmarkSqrtOnMersennePrime(b *testing.B) {
	b1 := sdk.NewDec(2).Power(127).Sub(sdk.OneDec())
	b.ReportAllocs()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		sink, _ = b1.ApproxSqrt()
	}

	if sink == nil {
		b.Fatal("Benchmark did not run")
	}
	sink = (interface{})(nil)
}

func BenchmarkQuoRoundupMut(b *testing.B) {
	b1 := sdk.NewDec(17e2 + 8371)
	baseArr := make([]sdk.Dec, b.N)
	for i := 0; i < b.N; i++ {
		baseArr[i] = b1.Clone()
	}
	b2 := sdk.NewDec(4371)
	b.ReportAllocs()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		sink = baseArr[i].QuoRoundupMut(b2)
	}

	if sink == nil {
		b.Fatal("Benchmark did not run")
	}
	sink = (interface{})(nil)
}

func TestNegativePrecisionPanic(t *testing.T) {
	require.Panics(t, func() {
		sdk.NewDecWithPrec(10, -1)
	})
}

func TestQuoMut(t *testing.T) {
	specs := map[string]struct {
		dividend, divisor          sdk.Dec
		expTruncated, expRoundedUp string
		expPanic                   bool
	}{
		"0.0000000000000000001": {
			dividend:     sdk.NewDecWithPrec(1, 18),
			divisor:      sdk.MustNewDecFromStr("10"),
			expRoundedUp: "0.000000000000000001",
			expTruncated: "0.000000000000000000",
		},
		"0.0000000000000000002": {
			dividend:     sdk.NewDecWithPrec(1, 18),
			divisor:      sdk.MustNewDecFromStr("5"),
			expRoundedUp: "0.000000000000000001",
			expTruncated: "0.000000000000000000",
		},
		"0.0000000000000000003": {
			dividend:     sdk.NewDecWithPrec(1, 18),
			divisor:      sdk.MustNewDecFromStr("3.333333333333333"),
			expRoundedUp: "0.000000000000000001",
			expTruncated: "0.000000000000000000",
		},
		"0.0000000000000000004": {
			dividend:     sdk.NewDecWithPrec(1, 18),
			divisor:      sdk.MustNewDecFromStr("2.5"),
			expRoundedUp: "0.000000000000000001",
			expTruncated: "0.000000000000000000",
		},
		"0.0000000000000000005": {
			dividend:     sdk.NewDecWithPrec(1, 18),
			divisor:      sdk.MustNewDecFromStr("2"),
			expRoundedUp: "0.000000000000000001",

			expTruncated: "0.000000000000000000",
		},
		"0.0000000000000000006": {
			dividend:     sdk.NewDecWithPrec(1, 18),
			divisor:      sdk.MustNewDecFromStr("1.666666666666666666"),
			expRoundedUp: "0.000000000000000001",

			expTruncated: "0.000000000000000000",
		},
		"0.0000000000000000007": {
			dividend:     sdk.NewDecWithPrec(1, 18),
			divisor:      sdk.MustNewDecFromStr("1.428571428571429"),
			expRoundedUp: "0.000000000000000001",

			expTruncated: "0.000000000000000000",
		},
		"0.0000000000000000008": {
			dividend:     sdk.NewDecWithPrec(1, 18),
			divisor:      sdk.MustNewDecFromStr("1.25"),
			expRoundedUp: "0.000000000000000001",

			expTruncated: "0.000000000000000000",
		},
		"0.0000000000000000009": {
			dividend:     sdk.NewDecWithPrec(1, 18),
			divisor:      sdk.MustNewDecFromStr("1.111111111111111"),
			expRoundedUp: "0.000000000000000001",

			expTruncated: "0.000000000000000000",
		},
		"-0.0000000000000000001": {
			dividend:     sdk.NewDecWithPrec(1, 18).Neg(),
			divisor:      sdk.MustNewDecFromStr("10"),
			expRoundedUp: "0.000000000000000000",
			expTruncated: "0.000000000000000000",
		},
		"-0.0000000000000000002": {
			dividend:     sdk.NewDecWithPrec(1, 18).Neg(),
			divisor:      sdk.MustNewDecFromStr("5"),
			expRoundedUp: "0.000000000000000000",
			expTruncated: "0.000000000000000000",
		},
		"-0.0000000000000000003": {
			dividend:     sdk.NewDecWithPrec(1, 18).Neg(),
			divisor:      sdk.MustNewDecFromStr("3.333333333333333"),
			expRoundedUp: "0.000000000000000000",
			expTruncated: "0.000000000000000000",
		},
		"-0.0000000000000000004": {
			dividend:     sdk.NewDecWithPrec(1, 18).Neg(),
			divisor:      sdk.MustNewDecFromStr("2.5"),
			expRoundedUp: "0.000000000000000000",
			expTruncated: "0.000000000000000000",
		},
		"-0.0000000000000000005": {
			dividend:     sdk.NewDecWithPrec(1, 18).Neg(),
			divisor:      sdk.MustNewDecFromStr("2"),
			expRoundedUp: "0.000000000000000000",
			expTruncated: "0.000000000000000000",
		},
		"-0.0000000000000000006": {
			dividend:     sdk.NewDecWithPrec(1, 18).Neg(),
			divisor:      sdk.MustNewDecFromStr("1.666666666666666666"),
			expRoundedUp: "0.000000000000000000",
			expTruncated: "0.000000000000000000",
		},
		"-0.0000000000000000007": {
			dividend:     sdk.NewDecWithPrec(1, 18).Neg(),
			divisor:      sdk.MustNewDecFromStr("1.428571428571429"),
			expRoundedUp: "0.000000000000000000",
			expTruncated: "0.000000000000000000",
		},
		"-0.0000000000000000008": {
			dividend:     sdk.NewDecWithPrec(1, 18).Neg(),
			divisor:      sdk.MustNewDecFromStr("1.25"),
			expRoundedUp: "0.000000000000000000",
			expTruncated: "0.000000000000000000",
		},
		"-0.0000000000000000009": {
			dividend:     sdk.NewDecWithPrec(1, 18).Neg(),
			divisor:      sdk.MustNewDecFromStr("1.111111111111111"),
			expRoundedUp: "0.000000000000000000",
			expTruncated: "0.000000000000000000",
		},
		"--0.0000000000000000001": {
			dividend:     sdk.NewDecWithPrec(1, 18).Neg(),
			divisor:      sdk.MustNewDecFromStr("-10"),
			expRoundedUp: "0.000000000000000001",
			expTruncated: "0.000000000000000000",
		},
		"--0.0000000000000000002": {
			dividend:     sdk.NewDecWithPrec(1, 18).Neg(),
			divisor:      sdk.MustNewDecFromStr("-5"),
			expRoundedUp: "0.000000000000000001",
			expTruncated: "0.000000000000000000",
		},
		"--0.0000000000000000003": {
			dividend:     sdk.NewDecWithPrec(1, 18).Neg(),
			divisor:      sdk.MustNewDecFromStr("-3.333333333333333"),
			expRoundedUp: "0.000000000000000001",
			expTruncated: "0.000000000000000000",
		},
		"--0.0000000000000000004": {
			dividend:     sdk.NewDecWithPrec(1, 18).Neg(),
			divisor:      sdk.MustNewDecFromStr("-2.5"),
			expRoundedUp: "0.000000000000000001",
			expTruncated: "0.000000000000000000",
		},
		"--0.0000000000000000005": {
			dividend:     sdk.NewDecWithPrec(1, 18).Neg(),
			divisor:      sdk.MustNewDecFromStr("-2"),
			expRoundedUp: "0.000000000000000001",
			expTruncated: "0.000000000000000000",
		},
		"--0.0000000000000000006": {
			dividend:     sdk.NewDecWithPrec(1, 18).Neg(),
			divisor:      sdk.MustNewDecFromStr("-1.666666666666666666"),
			expRoundedUp: "0.000000000000000001",
			expTruncated: "0.000000000000000000",
		},
		"--0.0000000000000000007": {
			dividend:     sdk.NewDecWithPrec(1, 18).Neg(),
			divisor:      sdk.MustNewDecFromStr("-1.428571428571429"),
			expRoundedUp: "0.000000000000000001",
			expTruncated: "0.000000000000000000",
		},
		"--0.0000000000000000008": {
			dividend:     sdk.NewDecWithPrec(1, 18).Neg(),
			divisor:      sdk.MustNewDecFromStr("-1.25"),
			expRoundedUp: "0.000000000000000001",
			expTruncated: "0.000000000000000000",
		},
		"--0.0000000000000000009": {
			dividend:     sdk.NewDecWithPrec(1, 18).Neg(),
			divisor:      sdk.MustNewDecFromStr("-1.111111111111111"),
			expRoundedUp: "0.000000000000000001",
			expTruncated: "0.000000000000000000",
		},
		"big / small": {
			dividend:     sdk.MustNewDecFromStr("999999999999999999"),
			divisor:      sdk.NewDecWithPrec(1, 18),
			expRoundedUp: "999999999999999999000000000000000000.000000000000000000",
			expTruncated: "999999999999999999000000000000000000.000000000000000000",
		},
		"divide by dividend": {
			dividend:     sdk.NewDecWithPrec(123, 0),
			divisor:      sdk.MustNewDecFromStr("123"),
			expRoundedUp: "1.000000000000000000",
			expTruncated: "1.000000000000000000",
		},
		"zero divided": {
			dividend:     sdk.NewDecWithPrec(0, 0),
			divisor:      sdk.MustNewDecFromStr("1"),
			expRoundedUp: "0.000000000000000000",
			expTruncated: "0.000000000000000000",
		},
		"zero divided by negative value": {
			dividend:     sdk.NewDecWithPrec(0, 0),
			divisor:      sdk.MustNewDecFromStr("-1"),
			expRoundedUp: "0.000000000000000000",
			expTruncated: "0.000000000000000000",
		},
		"zero divided by zero": {
			dividend: sdk.NewDecWithPrec(0, 0),
			divisor:  sdk.MustNewDecFromStr("0"),
			expPanic: true,
		},
		"divide by zero": {
			dividend: sdk.NewDecWithPrec(1, 0),
			divisor:  sdk.MustNewDecFromStr("0"),
			expPanic: true,
		},
	}
	for name, spec := range specs {
		t.Run(name, func(t *testing.T) {
			t.Run("round up", func(t *testing.T) {
				t.Parallel()
				if !spec.expPanic {
					got := spec.dividend.Clone().QuoRoundupMut(spec.divisor.Clone())
					require.Equal(t, spec.expRoundedUp, got.String())
					return
				}
				require.Panics(t, func() {
					_ = spec.dividend.Clone().QuoRoundupMut(spec.divisor.Clone())
				})
			})
			t.Run("truncate", func(t *testing.T) {
				t.Parallel()
				if !spec.expPanic {
					got := spec.dividend.Clone().QuoTruncateMut(spec.divisor.Clone())
					require.Equal(t, spec.expTruncated, got.String())
					return
				}
				require.Panics(t, func() {
					_ = spec.dividend.Clone().QuoTruncateMut(spec.divisor.Clone())
				})
			})
		})
	}
}

func Test_DocumentAsymmetry(t *testing.T) {
	zeroDec := sdk.ZeroDec()
	emptyDec := sdk.Dec{}

	zeroDecBz, err := zeroDec.Marshal()
	require.NoError(t, err)
	zeroDecJSON, err := zeroDec.MarshalJSON()
	require.NoError(t, err)

	emptyDecBz, err := emptyDec.Marshal()
	require.NoError(t, err)
	emptyDecJSON, err := emptyDec.MarshalJSON()
	require.NoError(t, err)

	// makes sense, zero and empty are semantically different and render differently
	require.NotEqual(t, zeroDecJSON, emptyDecJSON)
	// but on the proto wire they encode to the same bytes
	require.Equal(t, zeroDecBz, emptyDecBz)

	// zero values are symmetrical
	zeroDecRoundTrip := sdk.Dec{}
	err = zeroDecRoundTrip.Unmarshal(zeroDecBz)
	require.NoError(t, err)
	zeroDecRoundTripJSON, err := zeroDecRoundTrip.MarshalJSON()
	require.NoError(t, err)
	require.Equal(t, zeroDecJSON, zeroDecRoundTripJSON)
	require.Equal(t, zeroDec, zeroDecRoundTrip)

	// empty values are not
	emptyDecRoundTrip := sdk.Dec{}
	err = emptyDecRoundTrip.Unmarshal(emptyDecBz)
	require.NoError(t, err)
	emptyDecRoundTripJSON, err := emptyDecRoundTrip.MarshalJSON()
	require.NoError(t, err)

	// !!! this is the key point, they are not equal, it looks like a bug
	require.NotEqual(t, emptyDecJSON, emptyDecRoundTripJSON)
	require.NotEqual(t, emptyDec, emptyDecRoundTrip)
}

// 2^256 * 10^18 -1
const maxValidDecNumber = "115792089237316195423570985008687907853269984665640564039457584007913129639935999999999999999999"

func TestDecOpsWithinLimits(t *testing.T) {
	maxValid, ok := new(big.Int).SetString(maxValidDecNumber, 10)
	require.True(t, ok)
	minValid := new(big.Int).Neg(maxValid)
	specs := map[string]struct {
		src    *big.Int
		expErr bool
	}{
		"max": {
			src: maxValid,
		},
		"max + 1": {
			src:    new(big.Int).Add(maxValid, big.NewInt(1)),
			expErr: true,
		},
		"min": {
			src: minValid,
		},
		"min - 1": {
			src:    new(big.Int).Sub(minValid, big.NewInt(1)),
			expErr: true,
		},
		"max Int": {
			// max Int is 2^256 -1
			src: sdk.NewIntFromBigInt(new(big.Int).Sub(new(big.Int).Exp(big.NewInt(2), big.NewInt(256), nil), big.NewInt(1))).BigInt(),
		},
		"min Int": {
			// max Int is -1 *(2^256 -1)
			src: sdk.NewIntFromBigInt(new(big.Int).Neg(new(big.Int).Sub(new(big.Int).Exp(big.NewInt(2), big.NewInt(256), nil), big.NewInt(1)))).BigInt(),
		},
	}
	for name, spec := range specs {
		t.Run(name, func(t *testing.T) {
			src := sdk.NewDecFromBigIntWithPrec(spec.src, 18)

			ops := map[string]struct {
				fn func(src sdk.Dec) sdk.Dec
			}{
				"AddMut": {
					fn: func(src sdk.Dec) sdk.Dec { return src.AddMut(sdk.NewDec(0)) },
				},
				"SubMut": {
					fn: func(src sdk.Dec) sdk.Dec { return src.SubMut(sdk.NewDec(0)) },
				},
				"MulMut": {
					fn: func(src sdk.Dec) sdk.Dec { return src.MulMut(sdk.NewDec(1)) },
				},
				"MulTruncateMut": {
					fn: func(src sdk.Dec) sdk.Dec { return src.MulTruncateMut(sdk.NewDec(1)) },
				},
				"MulIntMut": {
					fn: func(src sdk.Dec) sdk.Dec { return src.MulIntMut(sdk.NewInt(1)) },
				},
				"MulInt64Mut": {
					fn: func(src sdk.Dec) sdk.Dec { return src.MulInt64Mut(1) },
				},
				"QuoMut": {
					fn: func(src sdk.Dec) sdk.Dec { return src.QuoMut(sdk.NewDec(1)) },
				},
				"QuoTruncateMut": {
					fn: func(src sdk.Dec) sdk.Dec { return src.QuoTruncateMut(sdk.NewDec(1)) },
				},
				"QuoRoundupMut": {
					fn: func(src sdk.Dec) sdk.Dec { return src.QuoRoundupMut(sdk.NewDec(1)) },
				},
			}
			for name, op := range ops {
				t.Run(name, func(t *testing.T) {
					if spec.expErr {
						assert.Panics(t, func() {
							got := op.fn(src)
							t.Log(got.String())
						})
						return
					}
					exp := src.String()
					// exp no panics
					got := op.fn(src)
					assert.Equal(t, exp, got.String())
				})
			}
		})
	}
}

func TestDecCeilLimits(t *testing.T) {
	maxValid, ok := new(big.Int).SetString(maxValidDecNumber, 10)
	require.True(t, ok)
	minValid := new(big.Int).Neg(maxValid)

	specs := map[string]struct {
		src    *big.Int
		exp    string
		expErr bool
	}{
		"max": {
			src:    maxValid,
			expErr: true,
		},
		"max + 1": {
			src:    new(big.Int).Add(maxValid, big.NewInt(1)),
			expErr: true,
		},
		"max - 1e18, previous full number": {
			src: new(big.Int).Sub(maxValid, new(big.Int).Exp(big.NewInt(10), big.NewInt(18), nil)),
			exp: "115792089237316195423570985008687907853269984665640564039457584007913129639935.000000000000000000",
		},
		"min": {
			src: minValid,
			exp: "-115792089237316195423570985008687907853269984665640564039457584007913129639935.000000000000000000",
		},
		"min - 1": {
			src:    new(big.Int).Sub(minValid, big.NewInt(1)),
			expErr: true,
		},
	}
	for name, spec := range specs {
		t.Run(name, func(t *testing.T) {
			src := sdk.NewDecFromBigIntWithPrec(spec.src, 18)
			if spec.expErr {
				assert.Panics(t, func() {
					got := src.Ceil()
					t.Log(got.String())
				})
				return
			}
			got := src.Ceil()
			assert.Equal(t, spec.exp, got.String())
		})
	}
}

func TestTruncateIntLimits(t *testing.T) {
	maxValid, ok := new(big.Int).SetString(maxValidDecNumber, 10)
	require.True(t, ok)
	minValid := new(big.Int).Neg(maxValid)

	specs := map[string]struct {
		src    *big.Int
		exp    string
		expErr bool
	}{
		"max": {
			src: maxValid,
			exp: "115792089237316195423570985008687907853269984665640564039457584007913129639935",
		},
		"max + 1": {
			src:    new(big.Int).Add(maxValid, big.NewInt(1)),
			expErr: true,
		},
		"min": {
			src: minValid,
			exp: "-115792089237316195423570985008687907853269984665640564039457584007913129639935",
		},
		"min - 1": {
			src:    new(big.Int).Sub(minValid, big.NewInt(1)),
			expErr: true,
		},
	}
	for name, spec := range specs {
		t.Run(name, func(t *testing.T) {
			src := sdk.NewDecFromBigIntWithPrec(spec.src, 18)
			if spec.expErr {
				assert.Panics(t, func() {
					got := src.TruncateInt()
					t.Log(got.String())
				})
				return
			}
			got := src.TruncateInt()
			assert.Equal(t, spec.exp, got.String())
		})
	}
}

func TestRoundIntLimits(t *testing.T) {
	maxValid, ok := new(big.Int).SetString(maxValidDecNumber, 10)
	require.True(t, ok)
	minValid := new(big.Int).Neg(maxValid)
	oneE18 := new(big.Int).Exp(big.NewInt(10), big.NewInt(18), nil)

	specs := map[string]struct {
		src    *big.Int
		exp    string
		expErr bool
	}{
		"max -1e18; previous full number": {
			src: new(big.Int).Sub(maxValid, oneE18),
			exp: "115792089237316195423570985008687907853269984665640564039457584007913129639935",
		},
		"max": {
			src:    maxValid,
			expErr: true,
		},
		"max + 1": {
			src:    new(big.Int).Add(maxValid, big.NewInt(1)),
			expErr: true,
		},
		"min + 1e18; previous full number": {
			src: new(big.Int).Add(minValid, oneE18),
			exp: "-115792089237316195423570985008687907853269984665640564039457584007913129639935",
		},
		"min": {
			src:    minValid,
			expErr: true,
		},
		"min - 1": {
			src:    new(big.Int).Sub(minValid, big.NewInt(1)),
			expErr: true,
		},
	}
	for name, spec := range specs {
		t.Run(name, func(t *testing.T) {
			src := sdk.NewDecFromBigIntWithPrec(spec.src, 18)
			t.Log(src.String())
			if spec.expErr {
				assert.Panics(t, func() {
					got := src.RoundInt()
					t.Log(got.String())
				})
				return
			}
			got := src.RoundInt()
			assert.Equal(t, spec.exp, got.String())
		})
	}
}

func BenchmarkIsInValidRange(b *testing.B) {
	maxValid, ok := new(big.Int).SetString(maxValidDecNumber, 10)
	require.True(b, ok)
	souceMax := sdk.NewDecFromBigIntWithPrec(maxValid, 18)
	b.ResetTimer()
	specs := map[string]sdk.Dec{
		"max":         souceMax,
		"greater max": sdk.NewDecFromBigIntWithPrec(maxValid, 16),
		"min":         souceMax.Neg(),
		"lower min":   sdk.NewDecFromBigIntWithPrec(new(big.Int).Neg(maxValid), 16),
		"zero":        sdk.ZeroDec(),
		"one":         sdk.OneDec(),
	}
	for name, source := range specs {
		b.Run(name, func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				_ = source.IsInValidRange()
			}
		})
	}
}
