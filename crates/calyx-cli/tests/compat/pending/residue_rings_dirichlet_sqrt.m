// Square roots of Dirichlet characters of odd order over finite fields
// (Magma 2.22 fails on these).
H<b, c> := DirichletGroup(35, GF(13));
Sqrt(c^2); Sqrt(c^2)^2 eq c^2;
Sqrt(H!1);
Sqrt(c^4);
Sqrt(DirichletGroup(9, GF(4)).1);
