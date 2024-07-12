SELECT
    /*+ FK(City.isPartOf_CountryId, Country.CountryId),FK(Person.isLocatedIn_CityId, City.CityId),FK(Forum_hasMember_Person.PersonId, Person.PersonId),FK(Post.Forum_containerOfId, Forum.ForumId),FK(Comment.replyOf_PostId, Post.PostId),FK(Comment_hasTag_Tag.CommentId, Comment.CommentId),FK(Tag.hasType_TagClassId, TagClass.TagClassId), PK(Forum_hasMember_Person.PersonId, Forum_hasMember_Person.ForumId), PK(Comment_hasTag_Tag.CommentId, Comment_hasTag_Tag.TagId) */
count(*)
FROM  
 City, Country, Person, Forum_hasMember_Person, Forum, Post, Comment, Comment_hasTag_Tag, Tag, TagClass
WHERE
  City.isPartOf_CountryId = Country.CountryId
  AND Person.isLocatedIn_CityId = City.CityId
  AND Forum_hasMember_Person.PersonId = Person.PersonId
  AND Forum.ForumId = Forum_hasMember_Person.ForumId
  AND Post.Forum_containerOfId = Forum.ForumId
  AND Comment.replyOf_PostId = Post.PostId
  AND Comment_hasTag_Tag.CommentId = Comment.CommentId
  AND Tag.TagId = Comment_hasTag_Tag.TagId
  AND Tag.hasType_TagClassId = TagClass.TagClassId;