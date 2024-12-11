import type {
  Country,
  EnglishTaxRates,
  ScottishTaxRates,
} from "./types";

const englandNiWalesTaxRates: EnglishTaxRates = {
      COUNTRY: "England/NI/Wales",
      // Income tax
      DEFAULT_PERSONAL_ALLOWANCE: 12_570,
      HIGHER_BRACKET: 50_270,
      ADDITIONAL_BRACKET: 125_140,
      BASIC_RATE: 0.2,
      HIGHER_RATE: 0.4,
      ADDITIONAL_RATE: 0.45,
      PERSONAL_ALLOWANCE_DROPOFF: 100_000,
      // Student loan repayments
      STUDENT_LOAN_PLAN_1_WEEKLY_THRESHOLD: 480.57,
      STUDENT_LOAN_PLAN_2_WEEKLY_THRESHOLD: 524.9,
      STUDENT_LOAN_PLAN_4_WEEKLY_THRESHOLD: 531.92,
      STUDENT_LOAN_PLAN_5_WEEKLY_THRESHOLD: 480,
      STUDENT_LOAN_REPAYMENT_AMOUNT: 0.09, // People on plans 1, 2, 4 + 5 repay 9% of the amount you earn over the threshold
      STUDENT_LOAN_POSTGRAD_WEEKLY_THRESHOLD: 403.84,
      STUDENT_LOAN_REPAYMENT_AMOUNT_POSTGRAD: 0.06, // People on postgrad plans repay 6% of the amount you earn over the threshold
      // National Insurance
      NI_MIDDLE_RATE: 0.08,
      NI_UPPER_RATE: 0.02,
      NI_MIDDLE_BRACKET: 242,
      NI_UPPER_BRACKET: 967,
      // Pension allowances
      PENSION_ANNUAL_ALLOWANCE: 60_000,
      PENSION_MINIMUM_ANNUAL_ALLOWANCE: 10_000,
      PENSION_ADJUSTED_LIMIT: 260_000
};

const scottishTaxRates: ScottishTaxRates = {
    COUNTRY: "Scotland",

    // Income tax
    DEFAULT_PERSONAL_ALLOWANCE: 12_570,

    STARTER_RATE: 0.19,
    BASIC_BRACKET: 14_877,
    BASIC_RATE: 0.2,
    INTERMEDIATE_BRACKET: 26_562,
    INTERMEDIATE_RATE: 0.21,
    HIGHER_BRACKET: 43_663,
    HIGHER_RATE: 0.42,
    ADVANCED_BRACKET: 75_001,
    ADVANCED_RATE: 0.45,
    TOP_BRACKET: 125_140,
    TOP_RATE: 0.48,

    PERSONAL_ALLOWANCE_DROPOFF: 100_000,
    // Student loan repayments
    STUDENT_LOAN_PLAN_1_WEEKLY_THRESHOLD: 480.57,
    STUDENT_LOAN_PLAN_2_WEEKLY_THRESHOLD: 524.9,
    STUDENT_LOAN_PLAN_4_WEEKLY_THRESHOLD: 531.92,
    STUDENT_LOAN_PLAN_5_WEEKLY_THRESHOLD: 480,
    STUDENT_LOAN_REPAYMENT_AMOUNT: 0.09, // People on plans 1, 2, 4 + 5 repay 9% of the amount you earn over the threshold
    STUDENT_LOAN_POSTGRAD_WEEKLY_THRESHOLD: 403.84,
    STUDENT_LOAN_REPAYMENT_AMOUNT_POSTGRAD: 0.06, // People on postgrad plans repay 6% of the amount you earn over the threshold
    // National Insurance
    NI_MIDDLE_RATE: 0.08,
    NI_UPPER_RATE: 0.02,
    NI_MIDDLE_BRACKET: 242,
    NI_UPPER_BRACKET: 967,
    // Pension allowances
    PENSION_ANNUAL_ALLOWANCE: 60_000,
    PENSION_MINIMUM_ANNUAL_ALLOWANCE: 10_000,
    PENSION_ADJUSTED_LIMIT: 260_000
};

export function getHmrcRates(country: Country): EnglishTaxRates | ScottishTaxRates {
    return country === "Scotland" ? scottishTaxRates : englandNiWalesTaxRates;
};

export function isScottishTaxRates(taxRates: EnglishTaxRates | ScottishTaxRates): taxRates is ScottishTaxRates {
  return taxRates.COUNTRY === "Scotland";
}