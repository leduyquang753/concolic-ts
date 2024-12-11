import { getHmrcRates } from "./hmrc";

import type { Country } from "./types";

// Calculates an individual's annual personal allowance, based on taxable annual income.
// Not yet supported: marriage allowance, blind person's allowance
export function calculatePersonalAllowance(country: Country, taxableAnnualIncome: number): number {
  const { PERSONAL_ALLOWANCE_DROPOFF, DEFAULT_PERSONAL_ALLOWANCE } = getHmrcRates(country);

  // £1 of personal allowance is reduced for every £2 of Income over £100,000
  let personalAllowanceDeduction =
    taxableAnnualIncome >= PERSONAL_ALLOWANCE_DROPOFF
      ? (taxableAnnualIncome - PERSONAL_ALLOWANCE_DROPOFF) / 2
      : 0;

  const sum = DEFAULT_PERSONAL_ALLOWANCE - personalAllowanceDeduction;
  
  // When beyond £125k taxable income, the personal allowance will reach zero.
  // Don't let the deduction go below zero, though.
  if (personalAllowanceDeduction < 0) {
    personalAllowanceDeduction = 0;
  }

  return sum < 0 ? 0 : sum;
};
