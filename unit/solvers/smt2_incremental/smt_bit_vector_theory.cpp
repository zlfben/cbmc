// Author: Diffblue Ltd.

#include <testing-utils/use_catch.h>

#include <solvers/smt2_incremental/smt_bit_vector_theory.h>
#include <solvers/smt2_incremental/smt_terms.h>

#include <util/mp_arith.h>

TEST_CASE("SMT bit vector predicates", "[core][smt2_incremental]")
{
  const smt_bit_vector_constant_termt two{2, 8};
  const smt_bit_vector_constant_termt three{3, 8};
  const smt_bool_literal_termt false_term{false};
  const smt_bit_vector_constant_termt wider{2, 16};
  SECTION("unsigned less than")
  {
    const auto function_application =
      smt_bit_vector_theoryt::unsigned_less_than(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvult", smt_bool_sortt{}));
    REQUIRE(function_application.get_sort() == smt_bool_sortt{});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(smt_bit_vector_theoryt::unsigned_less_than(false_term, two));
    CHECK_THROWS(smt_bit_vector_theoryt::unsigned_less_than(two, false_term));
    CHECK_THROWS(smt_bit_vector_theoryt::unsigned_less_than(wider, two));
    CHECK_THROWS(smt_bit_vector_theoryt::unsigned_less_than(two, wider));
  }
  SECTION("unsigned less than or equal")
  {
    const auto function_application =
      smt_bit_vector_theoryt::unsigned_less_than_or_equal(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvule", smt_bool_sortt{}));
    REQUIRE(function_application.get_sort() == smt_bool_sortt{});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(
      smt_bit_vector_theoryt::unsigned_less_than_or_equal(false_term, two));
    CHECK_THROWS(
      smt_bit_vector_theoryt::unsigned_less_than_or_equal(two, false_term));
    CHECK_THROWS(
      smt_bit_vector_theoryt::unsigned_less_than_or_equal(wider, two));
    CHECK_THROWS(
      smt_bit_vector_theoryt::unsigned_less_than_or_equal(two, wider));
  }
  SECTION("unsigned greater than")
  {
    const auto function_application =
      smt_bit_vector_theoryt::unsigned_greater_than(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvugt", smt_bool_sortt{}));
    REQUIRE(function_application.get_sort() == smt_bool_sortt{});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(
      smt_bit_vector_theoryt::unsigned_greater_than(false_term, two));
    CHECK_THROWS(
      smt_bit_vector_theoryt::unsigned_greater_than(two, false_term));
    CHECK_THROWS(smt_bit_vector_theoryt::unsigned_greater_than(wider, two));
    CHECK_THROWS(smt_bit_vector_theoryt::unsigned_greater_than(two, wider));
  }
  SECTION("unsigned greater than or equal")
  {
    const auto function_application =
      smt_bit_vector_theoryt::unsigned_greater_than_or_equal(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvuge", smt_bool_sortt{}));
    REQUIRE(function_application.get_sort() == smt_bool_sortt{});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(
      smt_bit_vector_theoryt::unsigned_greater_than_or_equal(false_term, two));
    CHECK_THROWS(
      smt_bit_vector_theoryt::unsigned_greater_than_or_equal(two, false_term));
    CHECK_THROWS(
      smt_bit_vector_theoryt::unsigned_greater_than_or_equal(wider, two));
    CHECK_THROWS(
      smt_bit_vector_theoryt::unsigned_greater_than_or_equal(two, wider));
  }
  SECTION("signed less than")
  {
    const auto function_application =
      smt_bit_vector_theoryt::signed_less_than(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvslt", smt_bool_sortt{}));
    REQUIRE(function_application.get_sort() == smt_bool_sortt{});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(smt_bit_vector_theoryt::signed_less_than(false_term, two));
    CHECK_THROWS(smt_bit_vector_theoryt::signed_less_than(two, false_term));
    CHECK_THROWS(smt_bit_vector_theoryt::signed_less_than(wider, two));
    CHECK_THROWS(smt_bit_vector_theoryt::signed_less_than(two, wider));
  }
  SECTION("signed less than or equal")
  {
    const auto function_application =
      smt_bit_vector_theoryt::signed_less_than_or_equal(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvsle", smt_bool_sortt{}));
    REQUIRE(function_application.get_sort() == smt_bool_sortt{});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(
      smt_bit_vector_theoryt::signed_less_than_or_equal(false_term, two));
    CHECK_THROWS(
      smt_bit_vector_theoryt::signed_less_than_or_equal(two, false_term));
    CHECK_THROWS(smt_bit_vector_theoryt::signed_less_than_or_equal(wider, two));
    CHECK_THROWS(smt_bit_vector_theoryt::signed_less_than_or_equal(two, wider));
  }
  SECTION("signed greater than")
  {
    const auto function_application =
      smt_bit_vector_theoryt::signed_greater_than(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvsgt", smt_bool_sortt{}));
    REQUIRE(function_application.get_sort() == smt_bool_sortt{});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(smt_bit_vector_theoryt::signed_greater_than(false_term, two));
    CHECK_THROWS(smt_bit_vector_theoryt::signed_greater_than(two, false_term));
    CHECK_THROWS(smt_bit_vector_theoryt::signed_greater_than(wider, two));
    CHECK_THROWS(smt_bit_vector_theoryt::signed_greater_than(two, wider));
  }
  SECTION("signed greater than or equal")
  {
    const auto function_application =
      smt_bit_vector_theoryt::signed_greater_than_or_equal(two, three);
    REQUIRE(
      function_application.function_identifier() ==
      smt_identifier_termt("bvsge", smt_bool_sortt{}));
    REQUIRE(function_application.get_sort() == smt_bool_sortt{});
    REQUIRE(function_application.arguments().size() == 2);
    REQUIRE(function_application.arguments()[0].get() == two);
    REQUIRE(function_application.arguments()[1].get() == three);
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS(
      smt_bit_vector_theoryt::signed_greater_than_or_equal(false_term, two));
    CHECK_THROWS(
      smt_bit_vector_theoryt::signed_greater_than_or_equal(two, false_term));
    CHECK_THROWS(
      smt_bit_vector_theoryt::signed_greater_than_or_equal(wider, two));
    CHECK_THROWS(
      smt_bit_vector_theoryt::signed_greater_than_or_equal(two, wider));
  }
}
