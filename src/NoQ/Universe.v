Class Universe (U:Type) :=
  { dom : U -> Type }.
Arguments dom {U _} _ : simpl never.