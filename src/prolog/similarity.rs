use std::collections::{HashMap, HashSet};

pub struct SimilarityTable {
    table: HashMap<(String, String), f32>,
    domain: HashSet<String>
}

impl SimilarityTable {
    pub fn new() -> Self {
        let table = HashMap::new();
        let domain = HashMap::new();

        SimilarityTable {
           table, domain
        }
    }

    pub fn insert(&self, name1: String, name2: String, value: f32) {
        if name1 < name2 {
           self.table.insert((name1, name2), value);
        } else {
            self.table.insert((name2, name1), value);
        }
        self.domain.insert(name1);
        self.domain.insert(name2);
    }

    pub fn get_similar(name: String) -> Vec<String> {

    }

}

pub fn parse_similarity_table(path: String) -> SimilarityTable {
    HashMap::new()
}