% Set up a graph

edge(a,b).
edge(a,c).
edge(b,e).
edge(c,d).
edge(d,e).
edge(a,f).
edge(c,f).
edge(e,a).
edge(f,e).

% Ask questions about a graph

path(a,d,[a,c,d])?
path(a,f,[a,f])?
path(a,f,[a,c,f])?
path(a,e,[a,b,e])?
path(a,e,[a,f,e])?
path(a,f,P)?
path(b,a,P)?
path(b,X,P)?

