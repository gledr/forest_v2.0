In this example a simple function consisting only out of three gates has been
implemented wrong. Instead of an XOR gate, the last gate has been implemented as 
an OR gate. 

By applying Forest and select variables we can detect, that the SAT solver always 
guides us to enable main_register_select_enable4 to solve the bug.
