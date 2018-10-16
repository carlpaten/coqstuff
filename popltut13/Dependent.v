Require Import Program.

Ltac dep_destruct E := try intros until E;
  let x := fresh "x" in
    remember E as x; simpl in x; dependent destruction x;
      try match goal with
            | [ H : _ = E |- _ ] => try rewrite <- H in *; clear H
          end.

