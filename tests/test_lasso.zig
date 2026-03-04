// Test runner for Lasso lookup tests. Imports zigz so module path includes full src/.
// Run with: zig build test-lasso (uses --test-filter "lasso_prover")
const zigz = @import("zigz");
// Pull in module so its tests are compiled and run when filtered
const _ = zigz.lookups;
