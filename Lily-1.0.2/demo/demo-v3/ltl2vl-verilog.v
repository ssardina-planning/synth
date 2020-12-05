//(G( cancel=1 -> X(go=1) )) ->    (G( req=1 -> (X(grant=1) + X(X(grant=1)) + X(X(X(grant=1))))) *     G( grant=1 -> X(grant=0)) *     G( cancel=1 -> X(grant=0 U go=1)))
module synthesis(grant,clk,cancel,req,go);
  input  clk,cancel,req,go;
  output grant;
  wire clk,grant,cancel,req,go;
  reg [2:0] state;

   assign grant = (state == 0)||(state == 3)||(state == 6);

  initial begin
    state = 4; //n32_1
  end
  always @(posedge clk) begin
    case(state)
    0: begin //n26_1n32_1n28_1
      if (cancel==0 && req==1) state = 5;
      if (cancel==0 && req==0) state = 4;
      if (cancel==1 && req==1) state = 1;
      if (req==0 && cancel==1) state = 2;
    end
    1: begin //n16_1n33_1n27_1
      if (cancel==1 && go==1) state = 6;
      if (go==0) state = 3;
      if (go==1 && cancel==0) state = 0;
    end
    2: begin //n16_1n33_1
      if (req==0 && cancel==0 && go==1) state = 4;
      if (req==0 && cancel==1 && go==1) state = 2;
      if (go==1 && cancel==0 && req==1) state = 5;
      if (go==0) state = 3;
      if (cancel==1 && go==1 && req==1) state = 6;
    end
    3: begin //fairstate
      state = 3;
    end
    4: begin //n32_1
      if (req==0 && cancel==1) state = 2;
      if (cancel==1 && req==1) state = 6;
      if (cancel==0 && req==0) state = 4;
      if (cancel==0 && req==1) state = 5;
    end
    5: begin //n32_1n16_1n28_1
      if (cancel==1) state = 6;
      if (cancel==0) state = 0;
    end
    6: begin //n25_1n33_1n27_1
      if (req==1 && go==1 && cancel==1) state = 1;
      if (go==0) state = 3;
      if (req==1 && cancel==0 && go==1) state = 5;
      if (cancel==0 && go==1 && req==0) state = 4;
      if (cancel==1 && req==0 && go==1) state = 2;
    end
    endcase
  end
endmodule //synthesis
