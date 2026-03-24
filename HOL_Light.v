Record Type' := is_Type' {
  type :> Type;
  point : type
}.

Arguments is_Type' {_}.

Canonical Structure arr a (b : Type') := {| type := a -> b; point := fun _ => point b |}.

Canonical Structure Prop' := is_Type' True.
Definition imp (P Q : Prop) := P -> Q.
Definition all {T : Type'} (P : T -> Prop) := forall t, P t.