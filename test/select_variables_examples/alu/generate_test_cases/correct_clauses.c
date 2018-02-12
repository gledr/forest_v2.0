 
	switch(c_opcode_in) {
	case ADD: 
	  result_out = c_side_a_in + c_side_b_in;
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

if (result_out == 0){
	 zero_out = 1;
   } else {
	 zero_out = 0;
   }

    int __result_check = (result_out == c_expected_out);
    int __zero_check = (zero_out == c_expected_zero_out);
    int __result = (__result_check + __zero_check) == 2;
    __VERIFIER_assert(__result);
}
