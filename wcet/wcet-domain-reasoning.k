require "naive-domain-reasoning.k"

module WCET-DOMAIN-REASONING
  imports NAIVE-DOMAIN-REASONING

  rule _ impliesBag .Bag => true

  rule isInt(#symMap(_)(_:OpCode)) => true [function, anywhere]

endmodule
