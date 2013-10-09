Require Import FP.Classes.Multiplicative.
Require Import FP.Data.Product.

Instance Type_Multiplicative : Multiplicative Type := { mult := Product }.