Section parametric.
  Variable T : Type.

  Fixpoint vector (n : nat) : Type :=
    match n with
      | 0 => unit
      | S n => prod T (vector n)
    end.
End parametric.

Section multi_mem.
  Variable T : Type.
  Variables mem addr val : Type.

  Section read.
    Variable read : mem -> addr -> option val.
    Variable m : mem.
  
    Fixpoint multi_read_addrs (n : nat) : vector addr n -> (vector val n -> T) -> option T :=
      match n as n return vector addr n -> (vector val n -> T) -> option T with
        | 0 => fun _ k => Some (k tt)
        | S n => fun a k =>
          match read m (fst a) with
            | None => None
            | Some v => multi_read_addrs n (snd a) (fun vs => k (v,vs))
          end
      end.
  End read.
  
  Section write.
    Variable write : addr -> val -> mem -> option mem.

    Fixpoint multi_write_addrs (n : nat) : vector addr n -> vector val n -> mem -> option mem :=
      match n as n return vector addr n -> vector val n -> mem -> option mem with
        | 0 => fun _ _ m => Some m
        | S n => fun a v m =>
          match write (fst a) (fst v) m with
            | None => None
            | Some m => multi_write_addrs n (snd a) (snd v) m
          end
      end.
  End write.

  Variable N : nat.
  Variable footprint : addr -> vector addr N.
  Variable implode : vector val N -> T.
  Variable explode : T -> vector val N.

  Definition multi_read (read : mem -> addr -> option val) (a : addr) (m : mem) : option T :=
    multi_read_addrs read m N (footprint a) implode.

  Definition multi_write (write : addr -> val -> mem -> option mem) (a : addr) (v : T) : mem -> option mem :=
    multi_write_addrs write N (footprint a) (explode v).
  
End multi_mem.

