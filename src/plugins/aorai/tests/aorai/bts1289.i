/* run.config
   OPT: -aorai-automata tests/aorai/bts1289.ya -load-module tests/aorai/Aorai_test.cmxs -aorai-test 1 -aorai-test-number @PTEST_NUMBER@ @NEEDS_WP_SHARE@
   OPT: -aorai-automata tests/aorai/bts1289-2.ya -load-module tests/aorai/Aorai_test.cmxs -aorai-test 1 -aorai-test-number @PTEST_NUMBER@ @NEEDS_WP_SHARE@
 */

void a(void) {}

void main(void)
{
	//@ loop assigns i;
	for (int i=0; i<10; ++i)
		a();
}

