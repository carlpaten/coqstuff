Ltac inv1 H :=
   (inversion H; fail)
     || (inversion H; [idtac]; clear H; try subst).
