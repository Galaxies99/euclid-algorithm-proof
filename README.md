# formalized Euclid Algorithm proof
Using the Coq library Z to prove the Euclid GCD Algorithm.

The following codes are the algorithm's implementation in C++.

```C++
int gcd(int a, int b) {
    if(b == 0) return a;
    else return gcd(b, a % b);
}
```

We use Coq to formalize the algorithm. (including negative numbers)

- In definition "Euclid", we define the algorithm in Coq.

- In "Euclid_divide", we proof that the return value must be a divisor of both a and b.

- In "Euclid_greatest", we proof that the return value must be the greatest divisor of a and b.

By combining the proofs above, we can say that the correctness of Euclid GCD Algorithm has been proved.

By the way, we also prove that **the algorithm's time complexity is O(log n)** .

- We define "step" as the iteration steps of the algorithm, the rest of the definition is the same as definition "Euclid". We call the new definition "Euclid_step".

- In "Euclid_count_log", we proof the following formula.
  $$
  2^{\frac{step - 1}{2}} \leq |x| + |y|
  $$
  where x and y are arguments and step is defined above.

  We believed the theorem can show the time complexity of the algorithm is O(log (x + y)), which is O (log n).

  - In the proof of the theorem, we prove some useful lemmas such as "Euclid_half_descending", and we use the trick of 2-step induction in the proof of "Euclid_count_log_strong".
  - We can easily get the lemma "Euclid_count_log_ge" after proving "Euclid_count_log_strong", but we need to prove that the conclusion still holds if |x| < |y|, so we prove lemma "Euclid_count_log_lt_step" to show that we only need one step to become the situation where |x| >= |y|, then we can use "Euclid_count_log_ge" to prove easily.

Last Update in Oct. 26th, 2019.

By Tony Fang (Galaxies), All rights reserved.
