void __VERIFIER_assert (int val);

#define ADD 0
#define SUB 1
#define INC 2
#define DEC 3

int main () {
	int c_side_a_in = 2;
	int c_side_b_in = 2;
	int c_opcode_in = DEC;
	int c_expected_out = 1;
	int c_expected_zero_out = 1;
	int result_out = 0;
	int zero_out;

 
	switch(c_opcode_in) {
	case ADD: 
	  result_out = c_side_a_in - c_side_b_in;
	  break;
	case SUB: 
	  result_out = c_side_a_in - c_side_b_in;
	  break;
	case INC: 
	  result_out = c_side_a_in + 1;
	  break;
	case DEC: 
	  result_out = c_side_a_in - 1;
	  break;
	}

//    zero_out = result_out == 0 ? 0 : 1;
// __VERIFIER_assert(zero_out == c_expected_zero_out);
    __VERIFIER_assert(result_out == c_expected_out);
}
