#!/bin/bash
#
# Comprehensive test runner for zigz zkVM
#
# Usage:
#   ./run_tests.sh           # Run all tests
#   ./run_tests.sh quick     # Run only integration tests
#   ./run_tests.sh unit      # Run only unit tests
#   ./run_tests.sh bench     # Run benchmarks

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Print colored output
print_header() {
    echo -e "${BLUE}===================================================${NC}"
    echo -e "${BLUE}$1${NC}"
    echo -e "${BLUE}===================================================${NC}"
}

print_success() {
    echo -e "${GREEN}✓ $1${NC}"
}

print_error() {
    echo -e "${RED}✗ $1${NC}"
}

print_info() {
    echo -e "${YELLOW}ℹ $1${NC}"
}

# Parse command line arguments
MODE=${1:-all}

case $MODE in
    quick)
        print_header "Running Integration Tests"
        zig build test-integration
        print_success "Integration tests passed!"
        ;;

    unit)
        print_header "Running Unit Tests"

        print_info "Testing field arithmetic..."
        zig build test-field

        print_info "Testing polynomials..."
        zig build test-poly

        print_info "Testing sumcheck protocol..."
        zig build test-sumcheck

        print_info "Testing ISA..."
        zig build test-isa

        print_info "Testing Lasso lookups..."
        zig build test-lasso

        print_info "Testing polynomial commitments..."
        zig build test-commit

        print_info "Testing VM state machine..."
        zig build test-vm

        print_info "Testing constraint generation..."
        zig build test-constraints

        print_info "Testing prover..."
        zig build test-prover

        print_info "Testing verifier..."
        zig build test-verifier

        print_success "All unit tests passed!"
        ;;

    bench)
        print_header "Running Benchmarks"
        zig build bench
        print_success "Benchmarks complete!"
        ;;

    all|*)
        print_header "Running Complete Test Suite"

        print_info "Phase 1/3: Unit Tests"
        zig build test-field
        zig build test-poly
        zig build test-sumcheck
        zig build test-isa
        zig build test-lasso
        zig build test-commit
        zig build test-vm
        zig build test-constraints
        zig build test-prover
        zig build test-verifier
        print_success "Unit tests passed!"

        echo ""
        print_info "Phase 2/3: Integration Tests"
        zig build test-integration
        print_success "Integration tests passed!"

        echo ""
        print_info "Phase 3/3: Benchmarks"
        zig build bench
        print_success "Benchmarks complete!"

        echo ""
        print_header "Test Summary"
        print_success "All tests passed!"
        print_info "The zigz zkVM is working correctly."
        ;;
esac

echo ""
