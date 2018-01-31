void __VERIFIER_assert (int val);

int main () {

	int a = 1;
	int b = 1;
	int c = 1;
	int y = 1;

	int z1 = a & b;  // AND
	int z2 = b | c;  // XOR --> BUG is here
	int f = z1 | z2; // OR

	__VERIFIER_assert(f == y);
}
