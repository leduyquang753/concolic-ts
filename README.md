# Concolic unit test data generation for TypeScript

This is an experimental tool for automatic generation of unit test inputs for TypeScript projects, developed as part of
Lê Duy Quang's university graduation thesis.

Currently, top-level functions using number, string and object types with fixed structures are supported, along with a
selection of statement types (`if`, `while`, C-style `for`, `break`, `return`,...). Called functions can also be mocked
by replacing their call expressions with injected return values.

To run, after installing dependencies, write the configuration file in `src/config.ts` based on the template provided in
`src/config.ts.template`, then compile using `tsc`. Run the compiled `dist/server.js` file to start the tool along with
its REST API.

Modified experiment projects from GitHub are placed in the `experiment-projects` branch. These projects are:

- [`scottbedard/utils`](https://github.com/scottbedard/utils)
- [`SavingTool/hmrc-income-tax`](https://github.com/SavingTool/hmrc-income-tax)
- [`taxcalcs/taxjs`](https://github.com/taxcalcs/taxjs)