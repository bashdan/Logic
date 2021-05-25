addn(0,X,X).
addn(succ(M),N,succ(P)) :- addn (M,N,P).

eqi(T,T).
eqi(int(C,Y),int(A,B)) :- addn(C,Y,Z) , addn(C, B, Z).


addi(int(S,0),int(U,0),int(Q,0)) :- addn(S,U,Q).
addi(int(0,S),int(0,U),int(0,Q)) :- addn(S,U,Q).

multn(0,X,0).
multn(succ(X),0,0).
multn(succ(X),succ(Y),W) :- addn(Z,succ(Y),W), multn(X,succ(Y),Z).

