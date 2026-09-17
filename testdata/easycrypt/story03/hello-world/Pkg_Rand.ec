(* Rand: n = n *)

require import AllCore Distr FMap Int IntDiv Types.

module Rand = {
  var ctr : int

  proc init() : unit = {
    ctr <- 0;
  }

  proc d_UsefulOracle() : (int * bits_n) option = {
    var ec_result : (int * bits_n) option <- None;
    var rand : bits_n;
    ctr <- ctr + 1;
    rand <$ dbits_n;
    ec_result <- Some (ctr, rand);
    return ec_result;
  }

  proc d_UselessOracle(x : int) : int option = {
    var ec_result : int option <- None;
    var rand : bits_n;
    if (x = 1) {
      rand <$ dbits_n;
      ec_result <- Some 1;
    } else {

    }
    return ec_result;
  }
}.
