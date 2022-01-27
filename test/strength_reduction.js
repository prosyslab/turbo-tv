function add_zero(x) {
	return x+0
}

%PrepareFunctionForOptimization(add_zero);
add_zero(10);
%OptimizeFunctionOnNextCall(add_zero);
add_zero(10);
