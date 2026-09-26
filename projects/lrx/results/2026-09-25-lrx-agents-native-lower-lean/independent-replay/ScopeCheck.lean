import LRX.LowerBoundNativeComplete
open LRX.BlockExchange LRX.LowerBoundExceptionalNative
example (n : Nat) (hn : 4 ≤ n) (w : List Op) (h : run w (List.finRange n) = (List.finRange n).reverse.rotate (n-2)) : n*(n-1)/2 ≤ w.length := LRX.LowerBoundNativeComplete.native_lower hn w h
#print LRX.LowerBoundNativeComplete.native_lower
#print axioms LRX.LowerBoundNativeComplete.native_lower
#check LRX.LowerBoundExceptionalEndpoint.target_values
