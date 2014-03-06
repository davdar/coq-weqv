Require Import FP.Core.
Require Import FP.Classes.Iso.
Require Import FP.Classes.Galois.

Class IsoFunctor (t:qtype -> qtype) (u:qtype -> qtype) :=
  { IsoFunctor_Iso :> forall {A B}, Iso A B -> Iso (t A) (u B) }.
Class GaloisFunctor (t:qtype -> qtype) (u:qtype -> qtype) :=
  { GaloisFunctor_Galois :> forall {A B}, Galois A B -> Galois (t A) (u B) }.
Class ProperFunctor (t:qtype -> qtype) :=
  { ProperFunctor_Iso :> IsoFunctor t t
  ; ProperFunctor_Galois :> GaloisFunctor t t
  }.