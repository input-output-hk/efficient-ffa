
require import AllCore Int IntDiv List StdOrder Bool.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.

require import JUtils JBigNum.

(* big numbers, nlimb representation  *)
clone import BN as BN.

op B = Word.modulus. 
import Word.

(* summation from 0..nlimbs  *)
op sigma f = bigi predT f 0 nlimbs.

op q : int.

(* shorthand definitions  *)
op NativeLHS (k_min u : int) 
                                (x y z : Word.t A.t) : int 
  = sigma (fun (i : int) => 
         sigma (fun (j : int) =>
               to_uint x.[i]  * to_uint y.[j] 
                * (B ^ (i + j) %% q)))
     - sigma (fun (i : int) => to_uint z.[i] 
         * (B ^ i %% q)) 
     - (u + k_min) * q.


op AuxLHS (m_k v_k : int) k_min l_min u 
   (x y z : Word.t A.t) : int 
  = sigma (fun (i : int) => 
      sigma (fun (j : int) =>
              to_uint x.[i]  * to_uint y.[j] 
                 * (B ^ (i + j) %% q %% m_k)))             
     - (sigma (fun (i : int) => to_uint z.[i] 
         * (B ^ i %% q %% m_k)))
     - u * (q %% m_k)
     - (k_min * q) %% m_k
     - (v_k + l_min) * m_k.
    (* k_min * (q %% m_k)   - (k_min * q) %% m_k *)

op AuxUB (m_k : int) k_min l_min : int 
  = (B - 1) ^ 2 * sigma (fun (i : int) => 
      sigma (fun (j : int) =>
              (B^(i + j) %% q %% m_k)))
     - (k_min * q) %% m_k
     - l_min * m_k.


op AuxLB (m_k : int) (k_min l_min u_max v_max : int) : int 
  = (-1) * (B - 1) * 
      sigma (fun (i : int) =>
           (B ^ i  %% q  %% m_k))
     - u_max * (q %% m_k) 
     - (k_min * q) %% m_k 
     - (v_max + l_min) * m_k.


op K_min = 
  (-1) * (((B - 1) * 
    (sigma (fun (i : int) => 
        (B ^ i) %% q))) %/ q).


op K_max : int = 
  (B - 1) ^ 2 * 
     (sigma (fun (i : int) => 
       sigma (fun (j : int) => 
         (B ^ (i + j) %% q)))) %/ q.


op U k = k - K_min. 

op L_min m u_max = 
  (-1) * (((B - 1) * 
    (sigma (fun (i : int) => 
        (B ^ i %% q) %% m)) 
   + u_max * (q %% m) 
   + (K_min * q) %% m) %/ m).


op L_max m = 
  ((B - 1) ^ 2 * 
     (sigma (fun (i : int) => 
       sigma (fun (j : int) => 
          (B ^ (i + j) %% q %% m)))) 
   - ((K_min * q) %% m) ) %/ m.
