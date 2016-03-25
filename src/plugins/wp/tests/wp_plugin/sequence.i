/* run.config
   OPT: -wp-model Caveat
 */

/* run.config_qualif
   OPT: -wp -wp-model Caveat -wp-proof alt-ergo
   OPT: -wp -wp-model Caveat -wp-proof why3:alt-ergo
*/

//@ ghost int call_seq;
/*@ axiomatic Call {
  @   logic \list<integer> call_obs{L} reads call_seq ;
  @   logic \list<integer> call_nil = [| |];
  @
  @ }
  @*/

/*@
  assigns call_seq;
  ensures call_obs == (\old(call_obs) ^ [| a |]);
*/
void f(int a);

/*@
  assigns call_seq;
  ensures call_obs == (\old(call_obs) ^ [| b |]);
*/
void g(int b);

//--- no calls -----------------------------------------

/*@
  requires init: call_obs == \Nil;
  assigns call_seq;
//  ensures m1: \length (call_obs) == 0;
//  ensures m2: \length (call_obs) == \length (call_nil);
  ensures n1: call_obs == \old(call_obs);
  ensures n2: call_obs == call_nil;
  ensures n3: call_obs == (call_nil ^ \old(call_obs) ^ \Nil);
//  ensures n4: call_obs == (\Nil ^ \old(call_obs) ^ call_nil);
//  ensures n5: call_obs == (call_nil *^ a);
//  ensures n6: call_obs == (\old(call_obs) *^ a);
 */
void no_calls(int a)
{ ;
}

//--- sequential call  ---------------------------------
/*@
  requires call_obs == \Nil;
  assigns call_seq;
  behavior g_called:
    assumes c!=0;
    ensures o1: \length (call_obs) == 3;
    ensures p1: call_obs == (\old(call_obs) ^ [| x, y, z |]);
    ensures p2: call_obs == (\old(call_obs) ^ [| x |] ^ [| y |] ^ [| z |] ^ \Nil);
    ensures p3: call_obs == (\old(call_obs) ^ [| x |] ^ \Nil ^ [| y |] ^ [| z |] ^ call_nil);
  behavior g_not_called:
    assumes c==0;
    ensures o2: \length (call_obs) == 2;
   ensures q1: call_obs == (\old(call_obs) ^ [| x, z |]);
   ensures q2: call_obs == (\old(call_obs) ^ [| x |] ^ ([| y |] *^ c) ^ [| z |] ^ \Nil);
   ensures q3: call_obs == (\old(call_obs) ^ [| x |] ^ call_nil ^ [| z |] ^ \Nil);
*/
void sequence(int c, int x, int y, int z)
{
  f(x);
  if (c)
    g(y);
  f(z);
}

//--- sequential call  ---------------------------------
/*@
  requires call_obs == \Nil;
  assigns call_seq;
  behavior g_called:
    assumes n>0;
    ensures u1: \length(call_obs) == 2 + n;
    ensures u2: call_obs == (\old(call_obs) ^ [| x |] ^ ([| y |] *^ n) ^ [| z |]);
  behavior g_not_called:
    assumes n<=0;
    ensures v1: \length(call_obs) == 2;
    ensures v2: call_obs == (\old(call_obs) ^ [| x, z |]);
*/
void loops(int n, int x, int y, int z)
{
  int i;
  f(x);
  /*@ loop assigns i, call_seq;
      loop invariant ok: id_min: 0 <= i;
      loop invariant ok: id_max: (0 <= n ? i <= n : i <= 0);
      loop invariant ok: inv: call_obs == (\at(call_obs,LoopEntry) ^ ([| y |] *^ i)) ;
  */
  for (i=0; i<n; i++)
    g(y);
  f(z);
}

//--- end ------------ ---------------------------------
