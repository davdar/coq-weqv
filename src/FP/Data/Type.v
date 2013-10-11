Require Import FP.Classes.Times.
Require Import FP.Classes.Plus.
Require Import FP.Data.Product.
Require Import FP.Data.Sum.

Instance Type_Times : Times Type := { times := Product }.
Instance Type_Plus : Plus Type := { plus := Sum }.