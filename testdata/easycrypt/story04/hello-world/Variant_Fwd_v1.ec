(* Fwd_v1: n = n *)

require import AllCore Distr FMap Int IntDiv Types.
require Interfaces.

module Fwd_v1 (P_Rand : Interfaces.Rand_i) = {
  var ctr : int

  proc init() : unit = {
    ctr <- 0;
  }

  proc d_UsefulOracle() : (int * bits_n) option = {
    var ec_result : (int * bits_n) option <- None;
    var y : (int * bits_n);
    var ec_r1 : (int * bits_n) option;
    ec_r1 <@ P_Rand.d_UsefulOracle();
    if (ec_r1 = None) {

    } else {
      y <- oget ec_r1;
      ec_result <- Some y;
    }
    return ec_result;
  }

  proc d_UselessOracle(x : int) : int option = {
    var ec_result : int option <- None;
    if (x = 1) {
      ec_result <- Some 1;
    } else {

    }
    return ec_result;
  }
}.
