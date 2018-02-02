 
	switch(c_opcode_in) {
	case ADD: 
	  result_out = c_side_a_in + c_side_b_in;
	  break;
	case SUB: 
	  result_out = c_side_a_in + c_side_b_in;
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
