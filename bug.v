Section Bug.

Variable local_blocks: nat->nat->option nat. 

Theorem thm: 
    forall slot: nat, 
    forall node1 node2: nat, 
    forall block3 block4: nat,
    forall x1 x2:nat,
    (forall block1 block2: nat, 
    local_blocks node1 slot = Some block1 -> 
    local_blocks node2 slot = Some block2 -> 
    block1 = block2) -> 
    local_blocks node1 (S slot) = Some block3 ->
    local_blocks node2 (S slot) = Some block4 ->
    block3 = block4.
    intros.
    apply H with (block1:=x1) (block2:=x2).

End Bug. 