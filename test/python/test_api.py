import pytest
from pybitwuzla import *

@pytest.fixture
def bzla():
    return Bitwuzla()

def test_new():
    Bitwuzla()


def test_set_term():
    # TODO
    pass


def test_terminate():
    # TODO
    pass


def test_copyright(bzla):
    assert bzla.copyright()


def test_version(bzla):
    assert bzla.version()


def test_git_id(bzla):
    # TODO
    #assert bzla.git_id()
    pass


def test_push(bzla):
    with pytest.raises(BitwuzlaException,
                       match=r"incremental usage not enabled"):
        bzla.push()
    bzla.set_option(Option.INCREMENTAL, True)
    bzla.push()
    bzla.push(3)


def test_pop(bzla):
    with pytest.raises(BitwuzlaException,
                       match=r"incremental usage not enabled"):
        bzla.pop()
    bzla.set_option(Option.INCREMENTAL, True)
    with pytest.raises(BitwuzlaException, match=r"number of levels to pop"):
        bzla.pop()
    bzla.push()
    bzla.pop()
    bzla.push(3)
    bzla.pop(3)


def test_assert_formula(bzla):
    # TODO
    pass


def test_check_sat(bzla):
    # TODO
    pass


def test_simplify(bzla):
    # TODO
    pass


def test_get_unsat_core(bzla):
    # TODO
    pass


def test_get_value(bzla):
    # TODO
    pass


def test_print_model(bzla):
    # TODO
    pass


def test_dump_formula(bzla):
    # TODO
    pass


def test_assume_formula(bzla):
    # TODO
    pass


def test_is_unsat_assumption(bzla):
    # TODO
    pass


def test_fixate_assumptions(bzla):
    # TODO
    pass


def test_reset_assumptions(bzla):
    # TODO
    pass


def test_get_unsat_assumptions(bzla):
    # TODO
    pass


def test_set_option(bzla):
    bzla.set_option(Option.PRODUCE_MODELS, 1)
    bzla.set_option(Option.INCREMENTAL, True)
    bzla.set_option(Option.SAT_ENGINE, "cadical")
    with pytest.raises(BitwuzlaException, match=r"invalid option value"):
        bzla.set_option(Option.SAT_ENGINE, "adical")


def test_get_option(bzla):
    bzla.set_option(Option.INCREMENTAL, True)
    assert bzla.get_option(Option.INCREMENTAL)
    bzla.set_option(Option.INCREMENTAL, False)
    assert not bzla.get_option(Option.INCREMENTAL)


def test_mk_bool_sort(bzla):
    bsort = bzla.mk_bool_sort()
    assert bsort.is_bv()
    assert bsort.bv_get_size() == 1


def test_mk_bv_sort(bzla):
    bsort = bzla.mk_bv_sort(32)
    assert bsort.is_bv()
    assert bsort.bv_get_size() == 32
    with pytest.raises(BitwuzlaException):
        bzla.mk_bv_sort(0)


def test_mk_array_sort(bzla):
    bv8 = bzla.mk_bv_sort(8)
    bv32 = bzla.mk_bv_sort(32)
    asort = bzla.mk_array_sort(bv32, bv8)
    assert asort.is_array()


def test_mk_fun_sort(bzla):
    bv8 = bzla.mk_bv_sort(8)
    bv32 = bzla.mk_bv_sort(32)
    bv64 = bzla.mk_bv_sort(64)
    fsort = bzla.mk_fun_sort([bv8, bv32, bv64], bv8)
    assert fsort.is_fun()


def test_mk_fp_sort(bzla):
    fp16 = bzla.mk_fp_sort(5, 11)
    assert fp16.is_fp()
    fp32 = bzla.mk_fp_sort(8, 24)
    assert fp32.is_fp()


def test_mk_rm_sort(bzla):
    rmsort = bzla.mk_rm_sort()
    assert rmsort.is_rm()


def test_mk_bv_value(bzla):
    bv_sort = bzla.mk_bv_sort(32)
    bzla.mk_bv_value(bv_sort, 123)
    bzla.mk_bv_value(bv_sort, "-123")
    bzla.mk_bv_value(bv_sort, "0x123")
    bzla.mk_bv_value(bv_sort, "#x1213")
    bzla.mk_bv_value(bv_sort, "0b101")
    bzla.mk_bv_value(bv_sort, "#b101")
    bzla.mk_bv_value(bv_sort, bin(123))
    bzla.mk_bv_value(bv_sort, hex(123))


def test_mk_bv_ones(bzla):
    bv_sort = bzla.mk_bv_sort(3)
    ones1 = bzla.mk_bv_ones(bv_sort)
    ones2 = bzla.mk_bv_value(bv_sort, -1)
    ones3 = bzla.mk_bv_value(bv_sort, "-1")
    ones4 = bzla.mk_bv_value(bv_sort, 7)
    ones5 = bzla.mk_bv_value(bv_sort, "7")
    ones6 = bzla.mk_bv_value(bv_sort, "0b111")
    ones7 = bzla.mk_bv_value(bv_sort, "#b111")
    ones8 = bzla.mk_bv_value(bv_sort, bin(7))
    assert ones1 == ones2
    assert ones2 == ones3
    assert ones3 == ones4
    assert ones4 == ones5
    assert ones5 == ones6
    assert ones6 == ones7
    assert ones7 == ones8


def test_mk_bv_min_signed(bzla):
    for i in range(16):
        bv_sort = bzla.mk_bv_sort(i+1)
        bvmin = bzla.mk_bv_min_signed(bv_sort)
        assert bvmin == bzla.mk_bv_value(bv_sort, "0b1" + "0" * i)


def test_mk_bv_max_signed(bzla):
    for i in range(16):
        bv_sort = bzla.mk_bv_sort(i+1)
        bvmax = bzla.mk_bv_max_signed(bv_sort)
        assert bvmax == bzla.mk_bv_value(bv_sort, "0b0" + "1" * i)


def test_mk_fp_value(bzla):
    try:
        rne = bzla.mk_rm_value(RoundingMode.RNE)
        fp16 = bzla.mk_fp_sort(5, 16)
        bzla.mk_fp_value(fp16, 0, 15, 1234)
        bzla.mk_fp_value(fp16, "1", 0b1100, "#b1110010010")
        bzla.mk_fp_value_from(fp16, rne, 0.31213)
        bzla.mk_fp_value_from(fp16, rne, 1/3)
        bzla.mk_fp_value_from(fp16, rne, "1/3")
        bzla.mk_fp_value_from(fp16, rne, "1.2/-3.03")
        bzla.mk_fp_value_from(fp16, rne, "-.123")

        with pytest.raises(BitwuzlaException, match=r"invalid value"):
            bzla.mk_fp_value_from(fp16, rne, "0..1")

    except BitwuzlaException as e:
        assert "SymFPU not configured" in e.msg


def test_mk_fp_pos_zero(bzla):
    # TODO
    pass


def test_mk_fp_neg_zero(bzla):
    # TODO
    pass


def test_mk_fp_pos_inf(bzla):
    # TODO
    pass


def test_mk_fp_neg_inf(bzla):
    # TODO
    pass


def test_mk_fp_nan(bzla):
    # TODO
    pass


def test_mk_const(bzla):
    # TODO
    pass


def test_mk_const_array(bzla):
    # TODO
    pass


def test_mk_var(bzla):
    # TODO
    pass


def test_mk_term(bzla):
    # TODO
    pass


def test_substitute(bzla):
    # TODO
    pass


# BitwuzlaSort tests
# TODO

# BitwuzlaTerm tests
# TODO
