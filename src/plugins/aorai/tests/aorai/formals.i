/* run.config
OPT: -aorai-automata tests/aorai/formals.ya -aorai-test 1 -load-module tests/aorai/Aorai_test.cmxs -aorai-test-number @PTEST_NUMBER@ @NEEDS_WP_SHARE@
*/

int f(int x) { return x; }

int g(int y) { return y; }

int main() { f(1); g(2); }
