use std::{cell::RefCell, fmt::Display, marker::PhantomData};

#[derive(Clone, Debug)]
pub struct CommaSep<Item, Coll>(RefCell<Option<Coll>>, PhantomData<Item>);

impl<Item, Coll> CommaSep<Item, Coll> {
    pub fn new(coll: Coll) -> Self {
        Self(RefCell::new(Some(coll)), PhantomData)
    }
}

impl<Item: Display, Coll: Iterator<Item = Item>> Display for CommaSep<Item, Coll> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut comma = "";
        for item in self.0.borrow_mut().take().unwrap() {
            write!(f, "{comma}{item}")?;
            comma = ", ";
        }
        Ok(())
    }
}
