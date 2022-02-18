



# Type Inference Beginner





## Code From

[Type inference for beginners — Part 1](https://medium.com/@dhruvrajvanshi/type-inference-for-beginners-part-1-3e0a5be98a4b)

[Type inference for beginners — Part 2 (Polymorphism)](https://medium.com/@dhruvrajvanshi/type-inference-for-beginners-part-2-f39c33ca9513)



## Result



```
------------------------
Test: 1 + 2
"Int"
------------------------
Test: true + false
"Type mismatch:
    Expected Int
    Found Bool"
------------------------
Test: let id = x -> x in id(i)
"Int"
------------------------
Test: let id = x -> x in id(true)
"Bool"
------------------------
Test: let id = x -> x in (id(1) == id(1)) == id(true)
"Bool"
```







