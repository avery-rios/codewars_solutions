#[cfg(feature = "local")]
use algebraic_lists::*;

#[cfg(test)]
mod tests {
use super::*;
        
#[test]
fn should_create_from_vec() {
  assert_eq!(Cons::from_iter(Vec::<i32>::new()), Cons::Null);
  
  assert_eq!(Cons::from_iter(vec![1,2,3,4,5]).to_vec(),
             vec![1,2,3,4,5]);
}


#[test]
fn should_filter() {
  assert_eq!(Cons::from_iter(vec![1,2,3,4,5])
                  .filter(|&n| n > 3)
                  .to_vec(),
             vec![4,5]);
                 
  assert_eq!(Cons::from_iter(vec![1,2,3,4,5])
                  .filter(|&n| n > 5),
             Cons::Null);
}


#[test]
fn should_map() {
  assert_eq!(Cons::from_iter(vec!["1","2","3","4","5"])
                  .map(str::parse::<i32>)
                  .map(Result::unwrap)
                  .to_vec(),
             vec![1,2,3,4,5]);
}


#[test]
fn should_filter_map() {
  assert_eq!(Cons::from_iter(vec![1,2,3,4,5])
                  .filter(|n| n % 2 == 0)
                  .map(|x| x.to_string())
                  .to_vec(),
             ["2","4"]);
}
}