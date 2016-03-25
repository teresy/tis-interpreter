/* run.config_qualif
   OPT: -wp -wp-proof alt-ergo
   OPT: -wp -wp-proof why3:alt-ergo
*/

/*@ 
  axiomatic Nth {
  logic integer f(integer a);

  lemma access_16_16:
  \forall integer k ; 0 <= k < 16 ==>
  \nth( [| f(0) , f(1) , f(2) ,  f(3) ,  f(4) ,  f(5) ,  f(6) ,  f(7) , 
           f(8) , f(9) , f(10) , f(11) , f(12) , f(13) , f(14) , f(15) |] , k ) == f(k) ;
           
  }
*/

