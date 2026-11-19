//! Kind, RoundingMode, and Result (test_api.cpp: Kind, RoundingMode, Result).

use bitwuzla::{Kind, RoundingMode, SatResult};

#[test]
fn kind_to_string_() {
    assert_eq!(Kind::Constant.to_string(), "CONSTANT");
    assert_eq!(Kind::ConstArray.to_string(), "CONST_ARRAY");
    assert_eq!(Kind::Variable.to_string(), "VARIABLE");
    assert_eq!(Kind::Value.to_string(), "VALUE");
    assert_eq!(Kind::And.to_string(), "AND");
    assert_eq!(Kind::Apply.to_string(), "APPLY");
    assert_eq!(Kind::ArraySelect.to_string(), "SELECT");
    assert_eq!(Kind::ArrayStore.to_string(), "STORE");
    assert_eq!(Kind::BvAdd.to_string(), "BV_ADD");
    assert_eq!(Kind::BvAnd.to_string(), "BV_AND");
    assert_eq!(Kind::BvAshr.to_string(), "BV_ASHR");
    assert_eq!(Kind::BvComp.to_string(), "BV_COMP");
    assert_eq!(Kind::BvConcat.to_string(), "BV_CONCAT");
    assert_eq!(Kind::BvDec.to_string(), "BV_DEC");
    assert_eq!(Kind::BvInc.to_string(), "BV_INC");
    assert_eq!(Kind::BvMul.to_string(), "BV_MUL");
    assert_eq!(Kind::BvNand.to_string(), "BV_NAND");
    assert_eq!(Kind::BvNeg.to_string(), "BV_NEG");
    assert_eq!(Kind::BvNor.to_string(), "BV_NOR");
    assert_eq!(Kind::BvNot.to_string(), "BV_NOT");
    assert_eq!(Kind::BvOr.to_string(), "BV_OR");
    assert_eq!(Kind::BvRedand.to_string(), "BV_REDAND");
    assert_eq!(Kind::BvRedor.to_string(), "BV_REDOR");
    assert_eq!(Kind::BvRedxor.to_string(), "BV_REDXOR");
    assert_eq!(Kind::BvRol.to_string(), "BV_ROL");
    assert_eq!(Kind::BvRor.to_string(), "BV_ROR");
    assert_eq!(Kind::BvSaddOverflow.to_string(), "BV_SADDO");
    assert_eq!(Kind::BvSdivOverflow.to_string(), "BV_SDIVO");
    assert_eq!(Kind::BvSdiv.to_string(), "BV_SDIV");
    assert_eq!(Kind::BvSge.to_string(), "BV_SGE");
    assert_eq!(Kind::BvSgt.to_string(), "BV_SGT");
    assert_eq!(Kind::BvShl.to_string(), "BV_SHL");
    assert_eq!(Kind::BvShr.to_string(), "BV_SHR");
    assert_eq!(Kind::BvSle.to_string(), "BV_SLE");
    assert_eq!(Kind::BvSlt.to_string(), "BV_SLT");
    assert_eq!(Kind::BvSmod.to_string(), "BV_SMOD");
    assert_eq!(Kind::BvSmulOverflow.to_string(), "BV_SMULO");
    assert_eq!(Kind::BvSrem.to_string(), "BV_SREM");
    assert_eq!(Kind::BvSsubOverflow.to_string(), "BV_SSUBO");
    assert_eq!(Kind::BvSub.to_string(), "BV_SUB");
    assert_eq!(Kind::BvUaddOverflow.to_string(), "BV_UADDO");
    assert_eq!(Kind::BvUdiv.to_string(), "BV_UDIV");
    assert_eq!(Kind::BvUge.to_string(), "BV_UGE");
    assert_eq!(Kind::BvUgt.to_string(), "BV_UGT");
    assert_eq!(Kind::BvUle.to_string(), "BV_ULE");
    assert_eq!(Kind::BvUlt.to_string(), "BV_ULT");
    assert_eq!(Kind::BvUmulOverflow.to_string(), "BV_UMULO");
    assert_eq!(Kind::BvUrem.to_string(), "BV_UREM");
    assert_eq!(Kind::BvUsubOverflow.to_string(), "BV_USUBO");
    assert_eq!(Kind::BvXnor.to_string(), "BV_XNOR");
    assert_eq!(Kind::BvXor.to_string(), "BV_XOR");
    assert_eq!(Kind::Distinct.to_string(), "DISTINCT");
    assert_eq!(Kind::Equal.to_string(), "EQUAL");
    assert_eq!(Kind::Exists.to_string(), "EXISTS");
    assert_eq!(Kind::Forall.to_string(), "FORALL");
    assert_eq!(Kind::FpAbs.to_string(), "FP_ABS");
    assert_eq!(Kind::FpAdd.to_string(), "FP_ADD");
    assert_eq!(Kind::FpDiv.to_string(), "FP_DIV");
    assert_eq!(Kind::FpEqual.to_string(), "FP_EQUAL");
    assert_eq!(Kind::FpFma.to_string(), "FP_FMA");
    assert_eq!(Kind::FpFp.to_string(), "FP_FP");
    assert_eq!(Kind::FpGeq.to_string(), "FP_GEQ");
    assert_eq!(Kind::FpGt.to_string(), "FP_GT");
    assert_eq!(Kind::FpIsInf.to_string(), "FP_IS_INF");
    assert_eq!(Kind::FpIsNan.to_string(), "FP_IS_NAN");
    assert_eq!(Kind::FpIsNeg.to_string(), "FP_IS_NEG");
    assert_eq!(Kind::FpIsNormal.to_string(), "FP_IS_NORMAL");
    assert_eq!(Kind::FpIsPos.to_string(), "FP_IS_POS");
    assert_eq!(Kind::FpIsSubnormal.to_string(), "FP_IS_SUBNORMAL");
    assert_eq!(Kind::FpIsZero.to_string(), "FP_IS_ZERO");
    assert_eq!(Kind::FpLeq.to_string(), "FP_LEQ");
    assert_eq!(Kind::FpLt.to_string(), "FP_LT");
    assert_eq!(Kind::FpMax.to_string(), "FP_MAX");
    assert_eq!(Kind::FpMin.to_string(), "FP_MIN");
    assert_eq!(Kind::FpMul.to_string(), "FP_MUL");
    assert_eq!(Kind::FpNeg.to_string(), "FP_NEG");
    assert_eq!(Kind::FpRem.to_string(), "FP_REM");
    assert_eq!(Kind::FpRti.to_string(), "FP_RTI");
    assert_eq!(Kind::FpSqrt.to_string(), "FP_SQRT");
    assert_eq!(Kind::FpSub.to_string(), "FP_SUB");
    assert_eq!(Kind::Iff.to_string(), "IFF");
    assert_eq!(Kind::Implies.to_string(), "IMPLIES");
    assert_eq!(Kind::Ite.to_string(), "ITE");
    assert_eq!(Kind::Lambda.to_string(), "LAMBDA");
    assert_eq!(Kind::Not.to_string(), "NOT");
    assert_eq!(Kind::Or.to_string(), "OR");
    assert_eq!(Kind::Xor.to_string(), "XOR");
    assert_eq!(Kind::BvExtract.to_string(), "BV_EXTRACT");
    assert_eq!(Kind::BvRepeat.to_string(), "BV_REPEAT");
    assert_eq!(Kind::BvRoli.to_string(), "BV_ROLI");
    assert_eq!(Kind::BvRori.to_string(), "BV_RORI");
    assert_eq!(Kind::BvSignExtend.to_string(), "BV_SIGN_EXTEND");
    assert_eq!(Kind::BvZeroExtend.to_string(), "BV_ZERO_EXTEND");
    assert_eq!(Kind::FpToFpFromBv.to_string(), "FP_TO_FP_FROM_BV");
    assert_eq!(Kind::FpToFpFromFp.to_string(), "FP_TO_FP_FROM_FP");
    assert_eq!(Kind::FpToFpFromSbv.to_string(), "FP_TO_FP_FROM_SBV");
    assert_eq!(Kind::FpToFpFromUbv.to_string(), "FP_TO_FP_FROM_UBV");
    assert_eq!(Kind::FpToSbv.to_string(), "FP_TO_SBV");
    assert_eq!(Kind::FpToUbv.to_string(), "FP_TO_UBV");
    // Every kind has a string representation.
    for &kind in Kind::ALL {
        assert!(!kind.to_string().is_empty());
    }
}

#[test]
fn rm_to_string_() {
    assert_eq!(RoundingMode::Rna.to_string(), "RNA");
    assert_eq!(RoundingMode::Rne.to_string(), "RNE");
    assert_eq!(RoundingMode::Rtn.to_string(), "RTN");
    assert_eq!(RoundingMode::Rtp.to_string(), "RTP");
    assert_eq!(RoundingMode::Rtz.to_string(), "RTZ");
}

#[test]
fn result_to_string_() {
    assert_eq!(SatResult::Sat.to_string(), "sat");
    assert_eq!(SatResult::Unsat.to_string(), "unsat");
    assert_eq!(SatResult::Unknown.to_string(), "unknown");
}
