void __VERIFIER_assert (int val);

#define DIM 8

int main () {

  int a[DIM] = {0,0,0,0,1,1,1,1};
  int b[DIM] = {0,0,1,1,0,0,1,1};
  int c[DIM] = {0,1,0,1,0,1,0,1};
  int y[DIM] = {0,1,1,1,0,1,0,0};

  for(int i = 0; i < DIM; ++i){
	int z1 = a[i] & b[i];
	int z2 = b[i] | c[i];
	int f = z1 | z2;

	__VERIFIER_assert(f = y[i]);
  }


}
