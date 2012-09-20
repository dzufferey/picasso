\universalConstants {
  int push1_7;
  int pop1_9;
  int x_16;
  int pop0_9;
  int push0_7;
  int x_15;
  int x_14;
  int v_8;
  int push1_6;
  int stack_7;
  int pop1_8;
  int v_7;
  int push1_54;
  int pop1_53;
  int v_52;
  int stack_31;
  int pop0_36;
  int pop1_51;
  int pop1_52;
  int x_97;
  int pop0_35;
  int push0_36;
  int x_94;
  int x_96;
  int x_95;
  int v_51;
  int push1_52;
  int push1_53;
}

\existentialConstants {
  int p_v_7;
  int p_pop1_8;
  int p_stack_7;
  int p_push1_6;
  int p_v_8;
  int p_x_14;
  int p_x_15;
  int p_push0_7;
  int p_pop0_9;
  int p_x_16;
  int p_pop1_9;
  int p_push1_7;
  int p_push1_56;
  int p_x_99;
  int p_pop1_55;
  int p_v_53;
  int p_v_54;
  int p_stack_32;
  int p_x_98;
  int p_pop1_54;
  int p_push0_37;
  int p_pop0_37;
  int p_x_100;
  int p_push1_55;
}


\problem {
  \exists int
      a_pop1_54, 
      a_push1_55, 
      a_v_53, 
      a_x_98, 
      a_v_54, 
      a_x_99, 
      a_stack_32, 
      a_push0_37, 
      a_pop0_37, 
      a_x_100, 
      a_pop1_55, 
      a_push1_56, 
      a_v_52, 
      a_x_94, 
      a_pop1_51, 
      a_x_95, 
      a_pop1_52, 
      a_push1_53, 
      a_pop1_53, 
      a_x_96, 
      a_pop0_35, 
      a_stack_31, 
      a_v_51, 
      a_x_97, 
      a_push0_36, 
      a_push1_54, 
      a_pop0_36, 
      a_push1_52; (
    v_52 = 1 &
    stack_31 = 1 &
    pop0_36 = 1 ->
      a_pop1_54=pop1_51 + pop1_52 &
      a_push1_55=push1_52 + push1_53 &
      a_v_53=v_51 &
      a_x_98=x_95 &
      a_v_54=v_52 &
      a_x_99=x_94 + x_96 &
      a_stack_32=stack_31 &
      a_push0_37=push0_36 &
      a_pop0_37=pop0_35 + pop0_36 &
      a_x_100=x_97 &
      a_pop1_55=pop1_53 &
      a_push1_56=push1_54 &
      a_v_52=0 &
      a_x_94=0 &
      a_pop1_51=0 &
      a_x_95=0 &
      a_pop1_52=0 &
      a_push1_53=0 &
      a_pop1_53=0 &
      a_x_96=0 &
      a_pop0_35=0 &
      a_stack_31=0 &
      a_v_51=0 &
      a_x_97=0 &
      a_push0_36=0 &
      a_push1_54=0 &
      a_pop0_36=0 &
      a_push1_52=0 &
      a_v_54 = 1 &
      a_stack_32 = 1 &
      p_v_7       =a_v_54 &
      p_pop1_8    =a_pop1_54 &
      p_stack_7   =a_stack_32 &
      p_push1_6   =a_push1_55 &
      p_v_8       =a_v_53 &
      p_x_14      =a_x_98 &
      p_x_15      =a_x_99 &
      p_push0_7   =a_push0_37 &
      p_pop0_9    =a_pop0_37 &
      p_x_16      =a_x_100 &
      p_pop1_9    =a_pop1_55 &
      p_push1_7   =a_push1_56 &
      p_push1_56  =0 &
      p_x_99      =0 &
      p_pop1_55   =0 &
      p_v_53      =0 &
      p_v_54      =0 &
      p_stack_32  =0 &
      p_x_98      =0 &
      p_pop1_54   =0 &
      p_push0_37  =0 &
      p_pop0_37   =0 &
      p_x_100     =0 &
      p_push1_55  =0
  )
}

/*
        push1_53 + push1_52 = p_push1_6 &
        v_51 = p_v_8 &
        x_95 = p_x_14 &
        x_96 + x_94 = p_x_15 &
        push0_36 = p_push0_7 &
        pop0_35 = p_pop0_9 -1 &
        x_97 = p_x_16 &
        pop1_52 + pop1_51 = p_pop1_8 &
        pop1_53 = p_pop1_9 &
        push1_54 = p_push1_7 &
        p_push1_55 = 0 &
        p_x_100 = 0 &
        p_pop0_37 = 0 &
        p_push0_37 = 0 &
        p_pop1_54 = 0 &
        p_x_98 = 0 &
        p_stack_32 = 0 &
        p_v_54 = 0 &
        p_v_53 = 0 &
        p_pop1_55 = 0 &
        p_x_99 = 0 & 
        p_push1_56 = 0 &
        p_stack_7 = 1 &
        p_v_7 = 1
*/
