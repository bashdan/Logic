append([], X, X).
append([X|Y],Z,[X|W]) :- append(Y,Z,W). 

elem(X, [X|Xs]).
elem(X, [Y|Ys]) :- elem(X, Ys).

prefix([],Ys).
prefix([X|Xs], [X|Ys]) :- prefix(Xs,Ys).

palindrome([]).
palindrome([Y]).
palindrome([X,X]).
palindrome([X|T]) :- append(M, [X], T), palindrome(M).

same(X,X).
same([X|Xs],[Y|Ys]) :- elem(X,Ys),elem(Y,Xs).

length([],0).
length([X|L],succ(N)) :- length(L,N).

