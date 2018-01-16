void __VERIFIER_assert (int val);

int main () {
 int a = 1;
 int b = 1;
 int c = 0;
 int y = 0;
 
 int tmp_1 = a & b;
 int tmp_2 = b | c;
 int f = tmp_1 | tmp_2;

 __VERIFIER_assert (f == y);
}
